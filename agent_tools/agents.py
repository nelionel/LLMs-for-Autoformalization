from langroid.agent.chat_agent import ChatAgent, ChatAgentConfig
from langroid.language_models.base import LLMMessage
import json

from agent_tools.agent_prompts import FORMALIZER_PROMPT, PARSER_PROMPT

class ParserAgent(ChatAgent):
    def __init__(self, config: ChatAgentConfig):
        config.system_message = PARSER_PROMPT
        super().__init__(config)

    def parse_proof(self, proof: str) -> str:
        """
        Parses a mathematical proof into a structured JSON representation.
        """
        messages = [
            LLMMessage(role="system", content=PARSER_PROMPT),
            LLMMessage(role="user", content=f"Please parse this proof into a structured JSON format:\n{proof}")
        ]
        response = self.llm_response_messages(messages)
        return response.content

class FormalizerAgent(ChatAgent):
    def __init__(self, config: ChatAgentConfig):
        config.system_message = FORMALIZER_PROMPT
        super().__init__(config)

    def formalize_to_lean(self, parsed_proof: str) -> str:
        """
        Translates a parsed proof into LEAN4 code.
        """
        messages = [
            LLMMessage(role="system", content=FORMALIZER_PROMPT),
            LLMMessage(role="user", content=f"Please formalize this parsed proof into Lean4 code:\n{parsed_proof}")
        ]
        response = self.llm_response_messages(messages)
        return response.content