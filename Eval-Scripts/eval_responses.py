import sys
 
# appending a path
<<<<<<< HEAD
sys.path.append('..')
=======
sys.path.append('../lean_tools')
>>>>>>> b727421c77aa1fddc161334de5d8e515f2d99a94
from lean_tools.execution import LeanExecution

lean = LeanExecution("./lean_project/LeanProject", "./lean_project/LeanOutputs"
)

lean.run("Test.lean", "console_output_test.txt", "interactive_output_test.txt")