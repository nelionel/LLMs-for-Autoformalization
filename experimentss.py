from lean_tools.execution import LeanExecution

lean = LeanExecution("./lean_project/LeanProject", "./lean_project/LeanOutputs"
)

lean.run("Test.lean", "console_output_test.txt", "interactive_output_test.txt")