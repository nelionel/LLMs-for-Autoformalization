# from pathlib import Path
# import re
# from tqdm import tqdm

# class MathlibCleaner:
#     def __init__(self, source_path: str, output_path: str):
#         self.source_path = Path(source_path)
#         self.output_path = Path(output_path)
        
#     def remove_comments(self, content: str) -> str:
#         """Remove /- -/ style comments from Lean code."""
#         # Remove multi-line comments with DOTALL
#         content = re.sub(r'/-[\s\S]*?-/','', content, flags=re.DOTALL)
#         # Remove single-line comments starting with --
#         content = re.sub(r'--.*$', '', content, flags=re.MULTILINE)
#         # Remove empty lines
#         content = '\n'.join(line for line in content.splitlines() if line.strip())
#         return content
    
#     def clean_file(self, file_path: Path):
#         """Clean a single Lean file and save it."""
#         try:
#             with open(file_path, 'r', encoding='utf-8') as f:
#                 content = f.read()
            
#             cleaned_content = self.remove_comments(content)
            
#             # Flatten path by joining parts with underscores
#             rel_path = file_path.relative_to(self.source_path)
#             new_filename = "_".join(rel_path.parts)
#             output_file = self.output_path / new_filename
            
#             self.output_path.mkdir(parents=True, exist_ok=True)
#             with open(output_file, 'w', encoding='utf-8') as f:
#                 f.write(cleaned_content)
                
#             print(f"Processed: {rel_path} -> {new_filename}")
            
#         except Exception as e:
#             print(f"Error processing {file_path}: {e}")
    
#     def process_all_files(self):
#         """Process all .lean files in the source directory."""
#         self.output_path.mkdir(parents=True, exist_ok=True)
        
#         all_files = list(self.source_path.rglob("*.lean"))
#         total_files = len(all_files)
#         print(f"Found {total_files} .lean files to process")
        
#         for file_path in tqdm(all_files, desc="Processing files"):
#             self.clean_file(file_path)

# # Usage
# cleaner = MathlibCleaner(
#     source_path="./lean_project/.lake/packages/mathlib/Mathlib",
#     output_path="./lean_project/LeanProject/CleanMathlib"
# )
# cleaner.process_all_files()

from pathlib import Path
import statistics
from collections import Counter
import matplotlib.pyplot as plt

class MathlibAnalyzer:
    def __init__(self, clean_mathlib_path: str):
        self.path = Path(clean_mathlib_path)
        
    def analyze_files(self):
        stats = {
            'file_count': 0,
            'word_counts': [],
            'file_sizes': []  # in KB
        }
        
        for file_path in self.path.rglob("*.lean"):
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                words = content.split()
                stats['word_counts'].append(len(words))
                stats['file_sizes'].append(file_path.stat().st_size / 1024)
                stats['file_count'] += 1
        
        # Calculate statistics
        wc = stats['word_counts']
        return {
            'total_files': stats['file_count'],
            'total_words': sum(wc),
            'avg_words': statistics.mean(wc),
            'median_words': statistics.median(wc),
            'std_dev_words': statistics.stdev(wc),
            'percentiles': {
                '10th': statistics.quantiles(wc, n=10)[0],
                '25th': statistics.quantiles(wc, n=4)[0],
                '75th': statistics.quantiles(wc, n=4)[2],
                '90th': statistics.quantiles(wc, n=10)[8]
            }
        }

# Usage
analyzer = MathlibAnalyzer("./lean_project/LeanProject/CleanMathlib")
stats = analyzer.analyze_files()
print(stats)