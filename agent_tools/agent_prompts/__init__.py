from importlib import resources

# Load prompts from txt files
with resources.open_text("agent_tools.agent_prompts", "formalizer.txt") as f:
    FORMALIZER_PROMPT = f.read()

with resources.open_text("agent_tools.agent_prompts", "parser.txt") as f:
    PARSER_PROMPT = f.read()

__all__ = ['FORMALIZER_PROMPT', 'PARSER_PROMPT']
