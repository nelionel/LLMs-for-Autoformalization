from agent_tools.agent_prompts import (
    GOAL_FINDER_PROMPT, 
    GOAL_TRANSLATOR_PROMPT, 
    NEXT_STEP_PROMPT, 
    NEXT_STEP_TRANSLATOR_PROMPT, 
    TRANSLATION_VERIFIER_PROMPT
)
import os
import openai
from typing import List, Optional, Callable, Dict, Any
from lean_tools.execution import LeanExecution
from pathlib import Path
from colorama import Fore, Style  # Add to imports

########################################
# Configuration
########################################

class BaseAgentConfig:
    def __init__(
        self, 
        openai_api_key: str,
        model_name: str = "gpt-4o",
        temperature: float = 0.0,
        system_message: Optional[str] = None,
        max_tokens: int = 2000,
        **kwargs
    ):
        self.openai_api_key = openai_api_key
        self.model_name = model_name
        self.temperature = temperature
        self.system_message = system_message
        self.max_tokens = max_tokens
        for k,v in kwargs.items():
            setattr(self, k, v)

########################################
# Message representation
########################################

class AgentMessage:
    def __init__(self, role: str, content: str):
        self.role = role
        self.content = content

    def to_dict(self):
        return {"role": self.role, "content": self.content}

########################################
# Base agent class
########################################

class BaseAgent:
    def __init__(self, config: BaseAgentConfig):
        self.config = config
        self.conversation: List[AgentMessage] = []
        if self.config.system_message:
            # For models that don't support system messages, use user role instead
            role = "user" if "o1-" in self.config.model_name else "system"
            self.conversation.append(AgentMessage(role, self.config.system_message))
        openai.api_key = self.config.openai_api_key
        self.name = self.__class__.__name__

    def add_message(self, role: str, content: str):
        self.conversation.append(AgentMessage(role, content))

    def get_messages_payload(self) -> List[dict]:
        return [m.to_dict() for m in self.conversation]

    def send(self, user_content: str, verbose: bool = False) -> str:
        """Send a message and get response, with optional colored logging"""
        self.add_message("user", user_content)
        
        if verbose:
            color_in = Colors.NATURAL_INPUT
            color_out = Colors.NATURAL
            
            if "Translator" in self.name:
                color_in = Colors.GENERATOR_INPUT
                color_out = Colors.GENERATOR
            elif "Verifier" in self.name:
                color_in = Colors.VERIFIER_INPUT
                color_out = Colors.VERIFIER
                
            print(f"\n{'='*50}")
            print(f"{color_in}{self.name} - Input:{Colors.RESET}")
            print(f"{'='*50}")
            print(f"{color_in}{user_content}{Colors.RESET}")
        
        # Set up parameters based on model type
        params = {
            "model": self.config.model_name,
            "messages": self.get_messages_payload(),
        }
        
        # Add model-specific parameters
        if "o1-" in self.config.model_name:
            params["max_completion_tokens"] = self.config.max_tokens
        else:
            params["max_tokens"] = self.config.max_tokens
        
        response = openai.ChatCompletion.create(**params)
        assistant_reply = response.choices[0].message["content"].strip()
        
        if verbose:
            # Show current tokens used vs max tokens from config
            total_tokens = response.usage.total_tokens
            
            print(f"\n{'='*50}")
            print(f"{color_out}{self.name} - Output: (Context: {total_tokens}/{self.config.max_tokens}){Colors.RESET}")
            print(f"{'='*50}")
            print(f"{color_out}{assistant_reply}{Colors.RESET}")
        
        self.add_message("assistant", assistant_reply)
        return assistant_reply

    def run(self, user_input: str) -> str:
        return self.send(user_input)

########################################
# Specialized agents
########################################

class GoalFinderAgent(BaseAgent):
    def __init__(self, config: BaseAgentConfig):
        config.system_message = GOAL_FINDER_PROMPT
        super().__init__(config)

    def find_goal(self, context: str) -> str:
        return self.run(context)

class TranslatorAgent(BaseAgent):
    def __init__(self, config: BaseAgentConfig):
        config.system_message = GOAL_TRANSLATOR_PROMPT
        super().__init__(config)

    def translate_to_lean(self, statement: str) -> str:
        return self.run(statement)

class NextStepAgent(BaseAgent):
    def __init__(self, config: BaseAgentConfig):
        config.system_message = NEXT_STEP_PROMPT
        super().__init__(config)

    def next_step(self, proof_state: str) -> Dict[str, Any]:
        # returns a natural language description of the next step
        response = self.run(proof_state)
        # You might parse response if needed. For now, just return as is.
        return {"type": "claim", "content": response}

class NextStepTranslatorAgent(BaseAgent):
    def __init__(self, config: BaseAgentConfig):
        config.system_message = NEXT_STEP_TRANSLATOR_PROMPT
        super().__init__(config)

    def translate_to_lean(self, input_text: str) -> str:
        """Standardized method name for consistency with other agents"""
        return self.run(input_text)

    # Keep the old method for backwards compatibility
    def translate_step_to_lean(self, current_lean_code: str, next_step: str) -> str:
        prompt = f"Current Lean code:\n{current_lean_code}\n\nNext step:\n{next_step}"
        return self.run(prompt)

class VerifierAgent(BaseAgent):
    def __init__(self, config: BaseAgentConfig):
        config.system_message = TRANSLATION_VERIFIER_PROMPT
        super().__init__(config)

    def verify(self, content: str) -> bool:
        verification_result = self.run(content)
        return "correct" in verification_result.lower() and "error" not in verification_result.lower()

########################################
# State Machine / Protocol
########################################

class PipelineState:
    """States for the proof formalization pipeline.
    The pipeline cycles through these states, building up the proof incrementally:
    1. FINDING_GOAL: Identify what needs to be proven
    2. TRANSLATING_GOAL: Convert the goal to Lean
    3. VERIFYING_GOAL: Check the goal translation
    4. FINDING_STEP: Determine next proof step
    5. TRANSLATING_STEP: Convert step to Lean
    6. VERIFYING_STEP: Verify step and add to proof if correct
    """
    FINDING_GOAL = "finding_goal"
    TRANSLATING_GOAL = "translating_goal"
    VERIFYING_GOAL = "verifying_goal"
    FINDING_STEP = "finding_step"
    TRANSLATING_STEP = "translating_step"
    VERIFYING_STEP = "verifying_step"
    SOLVED = "solved"
    ERROR = "error"

class ProofFormalizationPipeline:
    """
    A pipeline that incrementally builds a formal proof in Lean.
    Features two main loops:
    1. Goal formalization loop: Extract and formalize the initial goal
    2. Step formalization loop: Build the proof step by step
    
    Each successful verification resets the agents to their initial state,
    maintaining only the verified proof context.
    """
    MAX_TRANSLATION_ATTEMPTS = 5  # Maximum attempts for goal/step translation
    
    def __init__(
        self,
        goal_finder: GoalFinderAgent,
        goal_translator: TranslatorAgent,
        next_step_agent: NextStepAgent,
        next_step_translator: NextStepTranslatorAgent,
        verifier: VerifierAgent,
        initial_context: str,
        verbose: bool = False,
        run_id: str = "TestRun1"
    ):
        self.goal_finder = goal_finder
        self.goal_translator = goal_translator
        self.next_step_agent = next_step_agent
        self.next_step_translator = next_step_translator
        self.verifier = verifier
        self.verbose = verbose
        
        # Setup Lean execution paths
        self.run_id = run_id
        self.project_dir = Path("./lean_project/LeanProject")
        self.outputs_dir = Path("./lean_project/LeanOutputs")
        self.run_dir = self.project_dir / run_id
        self.run_outputs_dir = self.outputs_dir / f"{run_id}_Outputs"
        
        # Create directories if they don't exist
        self.run_dir.mkdir(parents=True, exist_ok=True)
        self.run_outputs_dir.mkdir(parents=True, exist_ok=True)
        
        # Initialize Lean execution with run-specific output directory
        self.lean = LeanExecution(str(self.project_dir), str(self.run_outputs_dir))
        
        # Initialize pipeline data
        self.current_state = PipelineState.FINDING_GOAL
        self.data = {
            "initial_context": initial_context,
            "natural_proof": "",
            "lean_code": "",
            "goal": "",
            "attempt_count": 0  # Track attempts for unique filenames
        }

    def reset_agents(self):
        """Reset all agents to their initial state with clean conversation histories."""
        for agent in [self.goal_finder, self.goal_translator, 
                     self.next_step_agent, self.next_step_translator, 
                     self.verifier]:
            # For o1 models, use 'user' role instead of 'system'
            role = "user" if "o1-" in agent.config.model_name else "system"
            agent.conversation = [AgentMessage(role, agent.config.system_message)]

    def get_current_context(self) -> str:
        """Build clean context with problem, goal, and verified steps."""
        context = f"""Initial problem:
{self.data['initial_context']}

Goal to prove:
{self.data['goal']}"""

        if self.data['natural_proof']:
            context += f"\n\nCurrent proof:\n{self.data['natural_proof']}"
        
        if self.data['lean_code']:
            context += f"\n\nCurrent Lean formalization:\n{self.data['lean_code']}"
        
        return context

    def run_lean_script(self, lean_code: str) -> str:
        """Execute Lean code and return console output."""
        attempt_num = self.data["attempt_count"]
        lean_file = f"{self.run_id}/{self.run_id}_attempt_{attempt_num}.lean"
        console_output = f"{self.run_id}_attempt_{attempt_num}_console.txt"
        interactive_output = f"{self.run_id}_attempt_{attempt_num}_interactive.txt"
        
        # Clean and validate Lean code
        if "```lean" not in lean_code:
            error_msg = "Error: No Lean code block markers found"
            if self.verbose:
                print(f"{Colors.GENERATOR}{error_msg}{Colors.RESET}")
            return error_msg
            
        clean_code = lean_code.split("```lean")[1].split("```")[0].strip()
        if not clean_code:
            error_msg = "Error: Empty Lean code block"
            if self.verbose:
                print(f"{Colors.GENERATOR}{error_msg}{Colors.RESET}")
            return error_msg
        
        # Write and execute
        lean_file_path = self.run_dir / f"{self.run_id}_attempt_{attempt_num}.lean"
        lean_file_path.write_text(clean_code)
        
        try:
            # Execute Lean and capture both console and interactive output
            self.lean.run(lean_file, console_output, interactive_output)
            
            # Read console output file
            console_output_path = self.run_outputs_dir / console_output
            print(f"DEBUG: Attempting to read from: {console_output_path.absolute()}")
            try:
                if console_output_path.exists():
                    with open(console_output_path, 'r') as f:
                        final_output = f.read().strip()
                        print(f"DEBUG: Successfully read file")
                    if not final_output:
                        final_output = "Lean execution completed without errors"
                else:
                    final_output = f"Error: Console output file not found at {console_output_path.absolute()}"
            except Exception as e:
                final_output = f"Error reading file: {str(e)}"
            
        except Exception as e:
            error_msg = f"Error executing Lean: {str(e)}"
            if self.verbose:
                print(f"{Colors.GENERATOR}{error_msg}{Colors.RESET}")
            return error_msg
        
        self.data["attempt_count"] += 1
        
        if self.verbose:
            print(f"\n{'='*50}")
            print(f"{Colors.GENERATOR}Lean Execution - Attempt {attempt_num}{Colors.RESET}")
            print(f"{Colors.GENERATOR}{final_output}{Colors.RESET}")
        
        return final_output

    def log_state_transition(self, new_state: str):
        """Log state transitions if verbose"""
        if self.verbose:
            print(f"\n{'='*50}")
            print(f"Pipeline State: {new_state}")
            print(f"{'='*50}")

    def formalize_goal(self) -> bool:
        """First main loop: Extract and formalize the initial goal."""
        # Extract goal
        goal = self.goal_finder.send(self.data["initial_context"], self.verbose)
        if not goal:  # Ensure we got a valid goal
            return False
        self.data["goal"] = goal
        
        # First translation attempt
        lean_code = self.goal_translator.send(f"""Goal to translate to Lean:
{self.data['goal']}""", self.verbose)
        
        if not lean_code or "```lean" not in lean_code:  # Basic validation
            if self.verbose:
                print(f"{Colors.GENERATOR}Invalid Lean code generated{Colors.RESET}")
            return False
        
        # Try to formalize goal with feedback loop
        for attempt in range(self.MAX_TRANSLATION_ATTEMPTS):
            console_output = self.run_lean_script(lean_code)
            result = self.verify_step(self.data["goal"], lean_code, console_output)
            
            if result == "All good" or result == "Solved":
                self.data["lean_code"] = lean_code
                break
            
            if "missing" in result.lower():  # Special handling for missing code error
                if self.verbose:
                    print(f"{Colors.VERIFIER}Verification failed: Missing code{Colors.RESET}")
                return False
            
            # If verification failed, get a new translation with the feedback
            lean_code = self.goal_translator.send(
                f"""Verification feedback: {result}
Please provide a corrected translation.""",
                self.verbose
            )
            
        if attempt >= self.MAX_TRANSLATION_ATTEMPTS - 1:
            return False
            
        self.reset_agents()
        return True

    def verify_step(self, natural_proof: str, lean_code: str, console_output: str) -> str:
        """Format verification input and get result."""
        if self.verbose:
            print(f"\n{'='*50}")
            print(f"{Colors.VERIFIER}Verification Step{Colors.RESET}")
            print(f"{'='*50}")
        
        verification_input = f"""Natural language proof:
{natural_proof}

Lean 4 code:
{lean_code}

Console output:
{console_output}"""
        
        # Pass verbose flag to send method to ensure proper agent attribution
        result = self.verifier.send(verification_input, self.verbose)
        
        if self.verbose:
            print(f"\n{'='*50}")
            print(f"{Colors.VERIFIER}Verification Result: {result}{Colors.RESET}")
            print(f"{'='*50}")
        
        return result

    def formalize_next_step(self) -> bool:
        """Second main loop: Formalize the next proof step."""
        # Reset agents at the start to clear any previous conversation
        self.reset_agents()
        
        # Format the context as per NextStepAgent's prompt
        context = f"""Natural Language: {self.data['initial_context']}
Partial proof:
{self.data['natural_proof'] if self.data['natural_proof'] else 'No steps taken yet.'}"""

        next_step_response = self.next_step_agent.send(context, self.verbose)
        
        # CRITICAL FIX: Check if we got a verification-like response
        if next_step_response in ["All good", "Solved"] or next_step_response.startswith("Error:"):
            if self.verbose:
                print(f"{Colors.ERROR}Invalid next step: Got a verification-style response{Colors.RESET}")
            return False
        
        if not next_step_response:
            if self.verbose:
                print(f"{Colors.NATURAL}No next step generated{Colors.RESET}")
            return False

        self.data["natural_proof"] += f"\n{next_step_response}"
        
        # First translation attempt
        full_lean_code = self.next_step_translator.send(f"""Current proof state:
{self.data['lean_code']}

Next step to integrate:
{next_step_response}""", self.verbose)

        # CRITICAL FIX: Check translator output
        if full_lean_code in ["All good", "Solved", "Error:"]:
            if self.verbose:
                print(f"{Colors.ERROR}Invalid translation: Got a verification-style response{Colors.RESET}")
            return False

        if not full_lean_code:
            if self.verbose:
                print(f"{Colors.GENERATOR}No Lean code generated{Colors.RESET}")
            return False
        
        # Try to formalize with feedback loop
        for attempt in range(self.MAX_TRANSLATION_ATTEMPTS):
            console_output = self.run_lean_script(full_lean_code)
            verification_result = self.verify_step(next_step_response, full_lean_code, console_output)
            
            if verification_result == "Solved" or verification_result == "All good":
                self.data["lean_code"] = full_lean_code
                # Don't return the verification result! Instead:
                if verification_result == "Solved":
                    return True
                break
            
            # If verification failed, get a new translation with the feedback
            full_lean_code = self.next_step_translator.send(f"""Verification feedback: {verification_result}
Please provide a corrected complete proof script.""", self.verbose)
            
            if not full_lean_code:
                if self.verbose:
                    print(f"{Colors.GENERATOR}No correction generated{Colors.RESET}")
                return False
            
        if attempt >= self.MAX_TRANSLATION_ATTEMPTS - 1:
            return False
            
        self.reset_agents()
        return False  # Return False unless we got "Solved"

    def run(self):
        """Main pipeline execution."""
        # First loop: Formalize the goal
        if not self.formalize_goal():
            self.current_state = PipelineState.ERROR
            return
        
        # Second loop: Build the proof step by step
        while self.current_state != PipelineState.ERROR:
            result = self.formalize_next_step()
            
            if not result:
                if self.current_state == PipelineState.SOLVED:
                    break  # Successfully completed
                self.current_state = PipelineState.ERROR
                break
            
            # Reset agents for next iteration
            self.reset_agents()

# Color constants for debugging
class Colors:
    NATURAL = Fore.GREEN
    NATURAL_INPUT = Fore.LIGHTGREEN_EX
    GENERATOR = Fore.YELLOW
    GENERATOR_INPUT = Fore.LIGHTYELLOW_EX
    VERIFIER = Fore.MAGENTA
    VERIFIER_INPUT = Fore.LIGHTMAGENTA_EX
    ERROR = Fore.RED
    RESET = Style.RESET_ALL

if __name__ == "__main__":
    # Get API key from environment variable
    api_key = os.getenv("OPENAI_API_KEY")
    if api_key is None:
        raise ValueError("Please set the OPENAI_API_KEY environment variable")

    # Setup configuration
    base_config = BaseAgentConfig(
        openai_api_key=api_key,
        model_name="o1-mini",  # or whatever model you're using
        temperature=0.0, 
        max_tokens=2048
    )

    # Initialize pipeline with agents
    pipeline = ProofFormalizationPipeline(
        goal_finder=GoalFinderAgent(base_config),
        goal_translator=TranslatorAgent(base_config),
        next_step_agent=NextStepAgent(base_config),
        next_step_translator=NextStepTranslatorAgent(base_config),
        verifier=VerifierAgent(base_config),
        initial_context="""From USAJMO 2024/25:

Question: 
Let $\mathbb{N}$ denote the set of positive integers. Find all functions $f : \mathbb{N} \rightarrow \mathbb{N}$ such that for positive integers $a$ and $b,$\[f(a^2 + b^2) = f(a)f(b) \text{ and } f(a^2) = f(a)^2.\]

Solution:
Claim: $f^2(m^2+n^2)=f(2mn)f(m^2-n^2)$ for all $m>n$.
Proof: The RHS equals $f((m^2-n^2)^2+(2mn)^2) = f((m^2+n^2)^2)=f^2(m^2+n^2)$ hence done $\blacksquare$.

Therefore $f(m)=f(n)=1$ implies $ f(2mn)=f(m^2-n^2)=1$ as well.

Note that $f(1)=1$ by the first condition and $f(2)=1$ by the second.

Now assume that for all integers $m$ up to $k \geq 2$, $f(m)=1$ holds.

If $k+1 \equiv 2 \pmod 4$, take $m,n$ such that $2mn=k+1$ and note that $m,n \leq \frac{k+1}{2} <k$ so $f(m)=f(n)=1$ by the inductive hypothesis hence $f(2mn)=f(k+1)=1$, so we are done.

If it is not $2 \pmod 4$ we may take $m>n$ such that $m^2-n^2=k+1$ and note that$$2n<2m=(m-n)+(m+n) \leq (m-n)(m+n)+1=k+2 \leq 2k,$$hence both $m,n$ are $\leq k$ so $f(m)=f(n)=1$ by the inductive hypothesis, therefore again $f(m^2-n^2)=f(k+1)=1$.

Thus, $f \equiv 1$ for all positive integers, which evidently satisfies, so it is our only solution.""",  # Your proof context here
        verbose=True  # Enable verbose logging
    )

    pipeline.run()