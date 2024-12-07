from langroid.agent.base import Agent
from langroid.agent.tool_message import ToolMessage
from langroid.language_models.openai_gpt import OpenAIGPTConfig
from langroid.utils.configuration import Settings, set_global
from langroid.agent.chat_document import ChatDocument
from typing import List
from pydantic import Field
import json
from importlib import resources

from agent_tools.agent_prompts import FORMALIZER_PROMPT, PARSER_PROMPT

class ParsingTool(ToolMessage):
    request: str = "parse_proof"
    purpose: str = "Analyze and dissect the given mathematical <proof> into its components."
    proof: str = Field(..., description="The mathematical proof text to be parsed.")

class FormalizerTool(ToolMessage):
    request: str = "formalize_to_lean"
    purpose: str = "Translate the parsed mathematical proof in <json_form> into valid LEAN4 code."
    json_form: str = Field(..., description="The JSON representation of the parsed proof.")

class ParserAgent(Agent):
    def __init__(self, config: OpenAIGPTConfig):
        super().__init__(config)
        self.config.system_message = PARSER_PROMPT

    def parse_proof(self, proof: str) -> str:
        """
        Parses a mathematical proof into a structured JSON representation.

        Args:
            proof: The natural language proof text.

        Returns:
            A JSON string representing the parsed proof structure.
        """
        response = self.llm_response(proof)
        if response and response.content:
            # Basic validation: Check if the response is valid JSON.
            try:
                json.loads(response.content)
                return response.content
            except json.JSONDecodeError:
                return "Error: Invalid JSON format in parsing output."
        else:
            return "Error: Empty response from parsing agent."

class FormalizerAgent(Agent):
    def __init__(self, config: OpenAIGPTConfig):
        super().__init__(config)
        self.config.system_message = FORMALIZER_PROMPT

    def formalize_to_lean(self, json_form: str) -> str:
        """
        Translates a parsed proof (in JSON format) into LEAN4 code.

        Args:
            json_form: The JSON string representing the parsed proof.

        Returns:
            A string containing the generated LEAN4 code.
        """
        response = self.llm_response(json_form)
        if response and response.content:
            # Consider adding basic validation or checks for common LEAN4 errors here.
            return response.content
        else:
            return "Error: Empty or invalid response from formalization agent."