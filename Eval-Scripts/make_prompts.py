import json
import os



#saves many .txt files , one for each prompt, into the prompts folder
output_path = 'prompts/'
path = 'all.jsonl'

def load_jsonl(file_path):
    with open(file_path, 'r') as file:
        return [json.loads(line) for line in file]

# Load data from the specified paths
data = load_jsonl(path)

# Create problem descriptions
string_descriptions = []
for entry in data:
    problem_description = (
        f"Formalize the following proof in lean 4.\n"
        f"Natural Language Statement: {entry['nl_statement']}\n"
        f"Natural Language Proof: {entry['nl_proof']}\n"
        f"Here is the beggining of the lean 4 file, containing the imports and the definition of the problem in lean 4. \n"
        f"This should be what you start your response with. Output only contents of the lean file, no extra messages. You may leave lean 4 comments"
        f"{entry['src_header']}"
        f"{entry['formal_statement']}"
    )
    string_descriptions.append(problem_description)

# Print the first problem description as a sample


os.makedirs(output_path, exist_ok=True)
for i, prompt in enumerate(string_descriptions):
    with open(os.path.join(output_path, f'prompt{i}.txt'), 'w') as file:
        file.write(prompt + '\n')
print(f"Responses saved to {output_path}")
