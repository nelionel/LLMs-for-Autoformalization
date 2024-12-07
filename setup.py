from setuptools import setup, find_packages

setup(
    name="formalization-tools",  # New umbrella name
    version="0.1.0",
    packages=find_packages(),
    package_data={
        "agent_tools.agent_prompts": ["*.txt"],
    },
    description="Tools for theorem proving with Lean",
    author="Ionel Chiosa",
    python_requires=">=3.6",
)