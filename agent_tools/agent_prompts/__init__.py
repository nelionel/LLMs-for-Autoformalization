from importlib import resources

# Load prompts from txt files
with resources.open_text("agent_tools.agent_prompts", "goal_finder.txt") as f:
    GOAL_FINDER_PROMPT = f.read()

with resources.open_text("agent_tools.agent_prompts", "goal_translator.txt") as f:
    GOAL_TRANSLATOR_PROMPT = f.read()

with resources.open_text("agent_tools.agent_prompts", "next_step.txt") as f:
    NEXT_STEP_PROMPT = f.read()

with resources.open_text("agent_tools.agent_prompts", "next_step_translator.txt") as f:
    NEXT_STEP_TRANSLATOR_PROMPT = f.read()

with resources.open_text("agent_tools.agent_prompts", "translation_verifier.txt") as f:
    TRANSLATION_VERIFIER_PROMPT = f.read()

# Export all prompts
__all__ = ['GOAL_FINDER_PROMPT', 'GOAL_TRANSLATOR_PROMPT', 'NEXT_STEP_PROMPT', 
           'NEXT_STEP_TRANSLATOR_PROMPT', 'TRANSLATION_VERIFIER_PROMPT']
