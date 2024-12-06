from dotenv import load_dotenv
import os
from openai import OpenAI
from lean_tools.execution import LeanExecution

class DummyAgent:
    def __init__(self, 
                 lean_files_dir,
                 output_dir,
                 system_prompt,
                 model="gpt-4o"):
        """
        Initialize DummyAgent.
        
        Args:
            lean_files_dir (str): Directory containing Lean files
            output_dir (str): Directory for outputs
            system_prompt (str, optional): System prompt for the model
            model (str): Model to use (default: "gpt-4")
        """
        # Load environment variables
        load_dotenv(dotenv_path=".env", override=True)
        
        # Debug print
        api_key = os.getenv('OPENAI_API_KEY')
        print(f"API Key loaded: {api_key[:10]}..." if api_key else "No API key found!")
        
        # Initialize OpenAI client
        self.client = OpenAI(api_key=os.getenv('FORMALIZE_API_KEY'))
        
        # Set up paths and configuration
        self.lean_files_dir = lean_files_dir
        self.output_dir = output_dir
        self.model = model
        
        # Initialize Lean execution
        self.lean = LeanExecution(lean_files_dir, output_dir)
        
        # Set default system prompt if none provided
        self.system_prompt = system_prompt 
    
    def generate_response(self, user_prompt):
        """Generate response from the model."""
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": self.system_prompt},
                {"role": "user", "content": user_prompt}
            ],
            response_format={"type": "text"}
        )
        return response.choices[0].message.content
    
    def save_and_check(self, content, filename):
        """Save content to a Lean file and check it."""
        # Clean the content (remove markdown if present)
        clean_content = content.replace("```lean", "").replace("```", "").strip()
        
        # Save to file
        file_path = os.path.join(self.lean_files_dir, filename)
        with open(file_path, 'w') as f:
            f.write(clean_content)
        
        # Run Lean check
        self.lean.run(filename,
                     console_output_path="console.txt",
                     interactive_output_path="interactive.txt")
        
        return {
            'console_output': self.lean.print_console(),
            'interactive_output': self.lean.print_interactive()
        }

# Example usage
if __name__ == "__main__":
    agent = DummyAgent(
        lean_files_dir="./lean_project/LeanProject",
        output_dir="./dummy_outputs", 
        system_prompt="You are a helpful assistant for Lean theorem proving. You provide the LEAN code ONLY, nothing else. No comments in the code. Just the solution."
    )
    
    # Example theorem to prove
    prompt = """
    Prove the following in Lean:
    For natural numbers a and b: (a + b)² = a² + 2ab + b²
    """
    
    # Generate and check response
    response = agent.generate_response(prompt)
    results = agent.save_and_check(response, "square_binomial.lean")
    
    print("\nConsole Output:")
    print(results['console_output'])
    print("\nInteractive Output:")
    print(results['interactive_output'])