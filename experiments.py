from openai import OpenAI
from rich import print as rprint
from agent_tools.agent_prompts import FORMALIZER_PROMPT, PARSER_PROMPT

# Initialize the client
client = OpenAI()  # Will use OPENAI_API_KEY from environment

# Create a function to replace ParserAgent
def parse_proof(proof_text):
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": PARSER_PROMPT},  # Use imported prompt
            {"role": "user", "content": proof_text}
        ],
        max_tokens=8000
    )
    return response.choices[0].message.content

# Create a function to replace FormalizerAgent
def formalize_to_lean(parsed_proof):
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": FORMALIZER_PROMPT},  # Use imported prompt
            {"role": "user", "content": parsed_proof}
        ],
        max_tokens=8000
    )
    return response.choices[0].message.content

# Create the base LLM configuration
llm_config = OpenAIGPTConfig(
    chat_model="gpt-4o",
    chat_context_length=8000,
)

# Create agent configs wrapping the LLM config
agent_config = ChatAgentConfig(
    llm=llm_config,
)

# Create agents (they handle their own prompts internally)
parser_gpt4 = ParserAgent(agent_config)
formalizer_gpt4 = FormalizerAgent(agent_config)

# Example test proof
test_proof = """
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

Thus, $f \equiv 1$ for all positive integers, which evidently satisfies, so it is our only solution.
"""

# Run experiment
parsed_gpt4 = parser_gpt4.parse_proof(test_proof)
formalized_gpt4 = formalizer_gpt4.formalize_to_lean(parsed_gpt4)

# Print results with color coding
print("\nExperiment Results:")
rprint("[orange3]Parser Output:[/orange3]")
rprint(f"[orange3]{parsed_gpt4}[/orange3]")
print("\n")
rprint("[green]Formalizer Output:[/green]")
rprint(f"[green]{formalized_gpt4}[/green]")
