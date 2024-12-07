from langroid.agent.agent import Agent
from langroid.agent.task import Task
from langroid.agent.tool_message import ToolMessage
from langroid.language_models.openai_gpt import OpenAIChatModel, OpenAIGPTConfig
from langroid.utils.configuration import Settings, set_global
from langroid.agent.chat_document import ChatDocument
from typing import List

class LeanVerificationTool(ToolMessage):
    request: str = "verify_lean_code"
    purpose: str = "Verify the provided <lean_code> using the Lean verifier and return the results."
    lean_code: str

class StrategistAgent(Agent):
    def __init__(self, config: OpenAIGPTConfig):
        super().__init__(config)
        self.config.system_message = """
            You are a Strategist Agent involved in a mathematical formalization project. You clearly understand the dependencies in mathematical proofs in natural langauge.
            You have the following task: Given a proof of a mathematical theorem in natural language, you identify the core theorems and lemmas that are used in the proof.
            As you identify them and understand the dependencies between theorems, lemmas, and definitions, you report the THEOREMS AND LEMMAS that are put together 
            in the final step of the proof.

            Example:
            The proof has 3 definitions, 5 lemmas (L1, ..., L5), and 3 theorems (T1, T2, T3), leading to the final theorem. 
            The proof start by introducing the definitions, proving lemmas 1 to 4. It uses these lemmas to prove T1 and T2. Then, it uses T2 to find L6. From L6 and theorem T1, it proves T3. Then, it puts together T1, T3 and L4 to prove the actual goal. 
            In this case, your output should be: the statements of T1, T3, and L6, as well as a description of how these results come together for the final proof. 
            3. Clearly articulate the sub-goals and the overall strategy 
               in natural language, using minimal, concise language.
            5. DO NOT attempt to formalize the sub-goals in Lean. 
               Only provide the strategy in natural language.
            6. ONLY OUTPUT the strategy, nothing else.
            7. For each goal/theorem, output it in natural language in
                the following format:
                [GOAL <number>]: <Natural language statement of the goal/theorem>
            8. If you believe that the decomposition is simple enough
                that it can be formalized, output:
                [GOAL]: DONE
            """

    def generate_strategy(self, problem: str, proof_sketch: str) -> List[str]:
        """
        Generates a proof strategy by decomposing a problem into sub-goals.

        Args:
            problem: The mathematical problem statement.
            proof_sketch: A natural language sketch of the proof.

        Returns:
            A list of natural language sub-goals.
        """

        prompt = f"""
        [PROBLEM]: {problem}
        [PROOF SKETCH]: {proof_sketch}
        
        Decompose the proof into a sequence of simpler sub-goals in natural language.
        """
        
        response = self.llm_response(prompt)
        
        if response is None or response.content is None:
            return []
        
        return response.content

class TranslatorAgent(Agent):
    def __init__(self, config: OpenAIGPTConfig, 
                 lean_verifier : LeanExecution): # Assuming you have a LeanExecution instance
        super().__init__(config)
        self.lean_verifier = lean_verifier
        self.config.system_message = """
            You are a Translator Agent, adept at converting natural language 
            mathematical statements and proof strategies into formal Lean code.
            You receive:
            1. A list of sub-goals (theorems) in natural language.
            2. Possibly, existing definitions or theorems in Lean.
            Your task is to:
            1. Translate each natural language sub-goal into a formal 
               Lean theorem, using `sorry` to mark unproven parts.
            2. Generate any necessary definitions required for the theorems.
            3. Ensure the generated Lean code is syntactically correct 
               and follows Lean's syntax and conventions.
            4. The output should be a MINIMAL, working Lean file, that only contains
               the necessary definitions, and the theorems to be proven, stated using sorry.
            5. Output ONLY the lean code.
            6. Verify your formalization using the `verify_lean_code` tool.
            7. Format your response as follows:
                ```lean
                -- Definitions (if any)
                -- Theorems (using sorry)
                ```
            """
        self.enable_message(LeanVerificationTool)

    def verify_lean_code(self, msg: LeanVerificationTool) -> str:
        """
        Verifies a Lean code snippet using the Lean verifier.

        Args:
            msg: The LeanVerificationTool message containing the code.

        Returns:
            The verification results from the Lean verifier.
        """
        
        results = self.lean_verifier.save_and_check(
            msg.lean_code, 
            "temp.lean"
        )
        
        return f"Lean verification results: {results}"

    def translate_to_lean(self, sub_goals: List[str]) -> str:
        """
        Translates a list of natural language sub-goals into formal Lean code.

        Args:
            sub_goals: A list of natural language sub-goals.

        Returns:
            A string containing the formalized Lean code.
        """
        
        prompt = f"""
        [SUB-GOALS]:
        """      
        
        for goal in sub_goals:
            prompt += goal + "\n"

        prompt += """
        
        Translate the sub-goals into formal Lean code, using `sorry` for unproven parts. 
        Generate necessary definitions.
        """
        
        response = self.llm_response(prompt)
        
        if response is None or response.content is None:
            return ""
        
        return response.content