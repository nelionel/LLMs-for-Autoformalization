import langroid as lr

cfg = lr.language_models.OpenAIGPTConfig(
    chat_model=lr.language_models.OpenAIChatModel.GPT4o,
)

mdl = lr.language_models.OpenAIGPT(cfg)

from langroid.language_models import Role, LLMMessage

msg = LLMMessage(
    content="what is the capital of Bangladesh?", 
    role=Role.USER
)

messages = [
    LLMMessage(content="You are really really sad.", role=Role.SYSTEM), 
    LLMMessage(content="What is the capital of Ontario?", role=Role.USER), 
]

response = mdl.chat(messages, max_tokens=200)

messages.append(response.to_LLMMessage())

from rich import print
from rich.prompt import Prompt 

messages = [
    LLMMessage(role=Role.SYSTEM, content="You are really really sad."),
]

while True:
    message = Prompt.ask("[blue]Human")
    if message in ["x", "q"]:
        print("[magenta]Bye!")
        break
    messages.append(LLMMessage(role=Role.USER, content=message))

    response = mdl.chat(messages=messages, max_tokens=200)
    messages.append(response.to_LLMMessage())