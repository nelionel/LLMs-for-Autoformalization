import openai
import os

#must be run from the 
#assumes the prompts folder has many .txt files, and asks the model to finish them
#saves responses as .lean files in the responses folder
# openai.api_key = 'ENTER'
eval_name = 'ProofNet'
prompts_dir = 'prompts'
responses_dir = '../lean_project/LeanProject/API_reponses'
model = 'gpt-4o'
limiter = 2 # how many responses to get


# Create a directory for responses if it doesn't exist
os.makedirs(responses_dir, exist_ok=True)


# Generate responses for a subset of problem descriptions for demonstration
prompt_files = [f for f in os.listdir(prompts_dir) if f.startswith('prompt') and f.endswith('.txt')]


# Function to get response using OpenAI ChatCompletion
def get_gpt3_response(prompt):
    response = openai.ChatCompletion.create(
        model=model,
        messages=[
            {"role": "user", "content": prompt}
        ],
    )
    return response.choices[0].message["content"].strip()


def extract_lean_code(text):
    lines = text.split('\n')
    # Remove lines that are just code fences
    # This assumes the code block uses ```lean at the start and ``` at the end.
    filtered_lines = [l for l in lines if not (l.strip().startswith('```'))]
    return '\n'.join(filtered_lines).strip()

for i, prompt_file in enumerate(prompt_files[:limiter]):
    with open(os.path.join(prompts_dir, prompt_file), 'r') as file:
        prompt = file.read()
    response = get_gpt3_response(prompt)
    response = extract_lean_code(response)
    
    # Save each response as a .lean file
    response_file_path = os.path.join(responses_dir, f'response_{i+1}.lean')
    with open(response_file_path, 'w') as response_file:
        response_file.write(response)



print(f"Responses saved in the '{responses_dir}' directory")
