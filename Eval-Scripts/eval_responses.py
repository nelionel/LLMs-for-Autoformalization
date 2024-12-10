import sys
 
# appending a path
sys.path.append('../lean_tools')
from lean_tools.execution import LeanExecution

outputs_dir = 'API_responses'
lean = LeanExecution("../lean_project/LeanProject/"+outputs_dir, "../lean_project/LeanProject/"+outputs_dir+"/LeanOutputs")


lean.run("response_1.lean", "console_output_test.txt", "interactive_output_test.txt")