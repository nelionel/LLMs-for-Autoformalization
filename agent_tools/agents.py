
from agent_tools.agent_prompts import FORMALIZER_PROMPT, PARSER_PROMPT
import os
import openai
from typing import List, Optional, Callable, Dict, Any

########################################
# Configuration
########################################

class BaseAgentConfig:
    """
    Configuration class for a generic agent interacting with an OpenAI model.
    Allows specifying API keys, models, temperature, etc.
    """
    def __init__(
        self, 
        openai_api_key: str,
        model_name: str = "gpt-4",
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
    """
    Represents a single message in a conversation thread.
    role: "system", "user", or "assistant"
    content: string content of the message
    """
    def __init__(self, role: str, content: str):
        self.role = role
        self.content = content

    def to_dict(self):
        return {"role": self.role, "content": self.content}


########################################
# Base agent class
########################################

class BaseAgent:
    """
    A base class for agents interacting with OpenAI models.

    This class:
     - Holds a conversation context as a list of messages.
     - Allows sending queries and receiving responses.
     - Can be extended for specialized roles (goal finder, translator, verifier, etc.)
    """

    def __init__(self, config: BaseAgentConfig):
        self.config = config
        self.conversation: List[AgentMessage] = []
        if self.config.system_message:
            self.conversation.append(AgentMessage("system", self.config.system_message))

        openai.api_key = self.config.openai_api_key

    def add_message(self, role: str, content: str):
        """
        Add a message to the conversation context.
        """
        self.conversation.append(AgentMessage(role, content))

    def get_messages_payload(self) -> List[dict]:
        """
        Convert the conversation into a list of dicts for the OpenAI API.
        """
        return [m.to_dict() for m in self.conversation]

    def send(self, user_content: str) -> str:
        """
        Send a user query to the model and get a response.
        """
        self.add_message("user", user_content)
        response = openai.ChatCompletion.create(
            model=self.config.model_name,
            messages=self.get_messages_payload(),
            temperature=self.config.temperature,
            max_tokens=self.config.max_tokens
        )
        assistant_reply = response.choices[0].message["content"].strip()
        self.add_message("assistant", assistant_reply)
        return assistant_reply

    def run(self, user_input: str) -> str:
        """
        High-level method to handle user input and return assistant response.
        You can override this method in subclasses if custom logic is needed.
        """
        return self.send(user_input)


########################################
# Specialized agents
########################################

class GoalFinderAgent(BaseAgent):
    """
    Identifies a goal (e.g., a theorem to prove, a target statement).
    """
    def find_goal(self, context: str) -> str:
        return self.run(context)


class TranslatorAgent(BaseAgent):
    """
    Translates given mathematical statements or claims into Lean 4 code.
    """
    def translate_to_lean(self, statement: str) -> str:
        return self.run(statement)


class VerifierAgent(BaseAgent):
    """
    Verifies the correctness of a statement, claim, or translation.
    This could be done by reasoning heuristics or by calling a proof assistant.
    """
    def verify(self, content: str) -> bool:
        # For now, just return True or False based on model output.
        # In a more advanced system, this could be integrated with a Lean server.
        verification_result = self.run(content)
        # Simple heuristic: Look for "correct" in the response.
        return "correct" in verification_result.lower()


class ProofStepAgent(BaseAgent):
    """
    Identifies the next logical step in the proof, either a definition or a claim.
    """
    def next_step(self, proof_state: str) -> Dict[str, Any]:
        """
        Return a structure specifying the next step type and content.
        Example return format:
        {
            "type": "claim", # or "definition"
            "content": "For all x, P(x) implies Q(x)."
        }
        """
        response = self.run(proof_state)
        # Here we assume the agent returns some structured text. 
        # In practice, you'd parse the response for structured data.
        # For now, we'll just return a mock dictionary.
        # Customize parsing as needed.
        return {"type": "claim", "content": response}


########################################
# Pipeline
########################################

class PipelineStep:
    """
    Represents a single step in the pipeline.
    A step has:
      - A descriptive name
      - A callable that runs the step
      - Inputs required by the step
      - Outputs produced by the step
    """
    def __init__(self, name: str, func: Callable[..., Any], inputs: List[str], outputs: List[str]):
        self.name = name
        self.func = func
        self.inputs = inputs
        self.outputs = outputs


class Pipeline:
    """
    A flexible pipeline to run a sequence of steps (agents or other functions).
    Each step can produce data that can be consumed by subsequent steps.
    Steps can be easily added, removed, or reordered.
    """
    def __init__(self):
        self.steps: List[PipelineStep] = []
        self.data: Dict[str, Any] = {}

    def add_step(self, step: PipelineStep):
        self.steps.append(step)

    def run(self, initial_data: Dict[str, Any]) -> Dict[str, Any]:
        self.data.update(initial_data)
        for step in self.steps:
            # Gather inputs
            kwargs = {inp: self.data[inp] for inp in step.inputs if inp in self.data}
            result = step.func(**kwargs)
            # If result is a dict, merge into data, else store under the first output name
            if isinstance(result, dict):
                self.data.update(result)
            else:
                if len(step.outputs) == 1:
                    self.data[step.outputs[0]] = result
                else:
                    # If multiple outputs are expected but we got a non-dict, handle accordingly
                    # For simplicity, just store under the first output name.
                    self.data[step.outputs[0]] = result
        return self.data


########################################
# Example usage
########################################

if __name__ == "__main__":
    # Setup configuration
    api_key = os.getenv("OPENAI_API_KEY")
    base_config = BaseAgentConfig(
        openai_api_key=api_key,
        model_name="gpt-4",
        temperature=0.0
    )

    # Instantiate agents with their system messages as needed
    # You can tailor these system messages based on the agent's role.
    goal_finder = GoalFinderAgent(BaseAgentConfig(
        openai_api_key=api_key,
        model_name="gpt-4",
        system_message="You are a helpful agent for finding mathematical goals."
    ))

    translator = TranslatorAgent(BaseAgentConfig(
        openai_api_key=api_key,
        model_name="gpt-4",
        system_message="You are a helpful agent that translates mathematical statements into Lean 4 code."
    ))

    verifier = VerifierAgent(BaseAgentConfig(
        openai_api_key=api_key,
        model_name="gpt-4",
        system_message="You are a verification agent that checks correctness of translations."
    ))

    proof_step_agent = ProofStepAgent(BaseAgentConfig(
        openai_api_key=api_key,
        model_name="gpt-4",
        system_message="You are a helpful agent that identifies the next step in a mathematical proof."
    ))

    # Define functions that wrap agent interactions for pipeline steps
    def find_goal_step(context: str):
        goal = goal_finder.find_goal(context)
        return {"goal": goal}

    def verify_goal_step(goal: str):
        # Imagine we have a translator and a verifier for the goal as well
        # For now, just return True assuming verification is done
        return {"goal_verified": True}

    def next_step_in_proof_step(goal: str):
        step = proof_step_agent.next_step(f"Current goal: {goal}\nPlease identify the next step.")
        return {"proof_step_type": step["type"], "proof_step_content": step["content"]}

    def translate_step(content: str):
        translation = translator.translate_to_lean(content)
        return {"lean_translation": translation}

    def verify_translation_step(lean_translation: str):
        is_correct = verifier.verify(f"Check correctness of this Lean code:\n{lean_translation}")
        return {"translation_verified": is_correct}

    # Create and configure a pipeline
    pipeline = Pipeline()

    # Add steps to the pipeline (this can be customized as needed)
    pipeline.add_step(PipelineStep(
        name="Find Goal",
        func=find_goal_step,
        inputs=["initial_context"], 
        outputs=["goal"]
    ))

    pipeline.add_step(PipelineStep(
        name="Verify Goal",
        func=verify_goal_step,
        inputs=["goal"],
        outputs=["goal_verified"]
    ))

    pipeline.add_step(PipelineStep(
        name="Find Next Proof Step",
        func=next_step_in_proof_step,
        inputs=["goal"],
        outputs=["proof_step_type", "proof_step_content"]
    ))

    pipeline.add_step(PipelineStep(
        name="Translate Step",
        func=translate_step,
        inputs=["proof_step_content"],
        outputs=["lean_translation"]
    ))

    pipeline.add_step(PipelineStep(
        name="Verify Translation",
        func=verify_translation_step,
        inputs=["lean_translation"],
        outputs=["translation_verified"]
    ))

    # Run the pipeline with some initial context
    initial_context = {
        "initial_context": "We want to formalize the given theorem about functions from N to N..."
    }

    final_data = pipeline.run(initial_context)
    print("Pipeline results:", final_data)

    # In a real system, you would loop and iterate based on conditions:
    # For example, continue identifying steps until the proof is complete,
    # or branch the pipeline based on verification results.
