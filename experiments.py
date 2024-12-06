from lean_tools.execution import LeanExecution

lean = LeanExecution("./lean_project/LeanProject", "./lean_project/LeanOutputs")
lean.run("Test.lean", 
         console_output_path="console_test.txt", 
         interactive_output_path="interactive_test_FAILED.txt"
         )

print(lean.print_console())
print(lean.print_interactive())