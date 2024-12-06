import subprocess
import os
import json
import time

class LeanExecution:
    def __init__(self, lean_files_dir, output_dir, max_execution_time=30):
        """
        Initialize LeanExecution object.
        
        Args:
            lean_files_dir (str): Directory containing Lean files
            output_dir (str): Path where output files will be stored
            max_execution_time (int): Maximum execution time in seconds for Lean processes
        """
        self.lean_files_dir = os.path.abspath(lean_files_dir)
        self.output_dir = os.path.abspath(output_dir)
        self.project_root = os.path.dirname(self.lean_files_dir)
        
        if not os.path.exists(os.path.join(self.project_root, 'lakefile.lean')):
            raise RuntimeError(f"Could not find lakefile.lean in {self.project_root}")
        
        self.max_execution_time = max_execution_time
        self.console_output = None
        self.interactive_output = None
        
        try:
            os.makedirs(self.output_dir, exist_ok=True)
        except OSError as e:
            raise RuntimeError(f"Could not create output directory at {self.output_dir}: {e}")
    
    def run(self, lean_filename, console_output_path=None, interactive_output_path=None):
        """
        Execute a Lean file and store/save its outputs.
        
        Args:
            lean_filename (str): Name of the Lean file (e.g., "New_file.lean")
            console_output_path (str, optional): Name of console output file
            interactive_output_path (str, optional): Name of interactive output file
        """
        file_path = os.path.join(self.lean_files_dir, lean_filename)
        if not os.path.exists(file_path):
            raise FileNotFoundError(f"Lean file not found: {file_path}")
        
        try:
            lean_file_abs_path = os.path.abspath(file_path)
            project_root = os.path.abspath(os.path.dirname(os.path.dirname(file_path)))
            env = self._get_lake_environment()
            
            start_time = time.time()
            print("Running Lean script: ", end="", flush=True)
            
            # Get console output
            self.console_output = self._execute_console(lean_file_abs_path, env, start_time)
            if console_output_path is not None:
                full_console_path = os.path.join(self.output_dir, console_output_path)
                with open(full_console_path, 'w') as f:
                    f.write(self.console_output)
            
            # Get interactive output
            self.interactive_output = self._execute_interactive(lean_file_abs_path, env, start_time)
            if interactive_output_path is not None:
                full_interactive_path = os.path.join(self.output_dir, interactive_output_path)
                with open(full_interactive_path, 'w') as f:
                    f.write(self.interactive_output)
                    
        except Exception as e:
            print(f"\nAn error occurred: {e}")
            raise
    
    def _get_lake_environment(self):
        """Get and parse Lake environment variables."""
        lake_env = subprocess.run(
            ['lake', 'env', 'printenv'],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=self.project_root
        )
        
        if lake_env.returncode != 0:
            raise RuntimeError(f"Failed to get Lake environment:\n{lake_env.stderr}")
            
        env = os.environ.copy()
        for line in lake_env.stdout.splitlines():
            if '=' in line:
                key, value = line.split('=', 1)
                env[key] = value
        return env
    
    def _execute_console(self, file_path, env, start_time):
        """Execute Lean file and get console output."""
        process = subprocess.Popen(
            ['lean', '--json', file_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=env,
            cwd=self.project_root
        )
        
        try:
            while process.poll() is None:
                elapsed = time.time() - start_time
                print(f"\rRunning Lean script: {elapsed:.2f}s (max time {self.max_execution_time}s)", end="", flush=True)
                time.sleep(0.1)
            
            output, errors = process.communicate(timeout=self.max_execution_time)
            print()  # New line after completion
            return output + (f"\nErrors:\n{errors}" if errors else "")
            
        except subprocess.TimeoutExpired:
            process.kill()
            output, errors = process.communicate()
            elapsed = time.time() - start_time
            print(f"\nExecution timed out after {elapsed:.2f} seconds")
            raise
    
    def _execute_interactive(self, file_path, env, start_time):
        """Execute Lean file and get interactive output."""
        process = subprocess.Popen(
            ['lake', 'env', 'lean', file_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=env,
            cwd=self.project_root
        )
        
        try:
            output, errors = process.communicate(timeout=self.max_execution_time)
            formatted_output = f"{file_path}:2:0\nNo info found.\nAll Messages (0)\nNo messages."
            return formatted_output + (f"\nErrors:\n{errors}" if errors else "")
            
        except subprocess.TimeoutExpired:
            process.kill()
            output, errors = process.communicate()
            elapsed = time.time() - start_time
            print(f"\nExecution timed out after {elapsed:.2f} seconds")
            raise
    
    def print_console(self):
        """
        Returns a nicely formatted version of the console output.
        Each JSON message is formatted with first-level nesting only.
        Skips fileName and kind fields for cleaner output.
        """
        if not self.console_output:
            return "LEAN CONSOLE OUTPUT:\n\tNo output available"
        
        formatted = "LEAN CONSOLE OUTPUT:"
        
        # Process each line as a separate JSON object
        for i, line in enumerate(self.console_output.splitlines()):
            if line.strip():  # Skip empty lines
                try:
                    data = json.loads(line)
                    formatted += f"\n\tJSON {i+1}:\n"
                    for key, value in data.items():
                        # Skip fileName and kind fields
                        if key not in ['fileName', 'kind']:
                            formatted += f"\t\t{key}: {value}\n"
                except json.JSONDecodeError:
                    formatted += f"\n\t\t{line}"
                
        return formatted
    
    def print_interactive(self):
        """
        Returns a nicely formatted version of the interactive output.
        Removes the file path line and adds indentation.
        """
        if not self.interactive_output:
            return "LEAN INTERACTIVE OUTPUT:\n\tNo output available"
        
        lines = self.interactive_output.splitlines()
        # Skip the first line (file path)
        formatted_lines = [f"\t{line}" for line in lines[1:] if line.strip()]
        
        return "LEAN INTERACTIVE OUTPUT:\n" + "\n".join(formatted_lines)

# Example usage
if __name__ == "__main__":
    project_root = "/Users/lonel-emilionichiosa/Desktop/new_formalize"
    lean = LeanExecution(project_root, project_root)
    lean.run(
        "./lean_stuff/LeanStuff/New_file.lean"
    )