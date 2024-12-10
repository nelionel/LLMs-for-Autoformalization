import json
from pathlib import Path
import numpy as np
from typing import List, Dict

class ProofNetDataset:
    def __init__(self, jsonl_path: str):
        self.examples = self._load_jsonl(jsonl_path)
        self.test_examples = [ex for ex in self.examples if ex["split"] == "test"]
        self.valid_examples = [ex for ex in self.examples if ex["split"] == "valid"]
        
    def _load_jsonl(self, path: str) -> List[Dict]:
        examples = []
        with open(path, 'r') as f:
            for line in f:
                examples.append(json.loads(line))
        return examples
    
    def save_splits(self, output_dir: str):
        Path(output_dir).mkdir(exist_ok=True)
        
        # Save test set
        with open(f"{output_dir}/test.jsonl", 'w') as f:
            for ex in self.test_examples:
                f.write(json.dumps(ex) + '\n')
                
        # Save validation set  
        with open(f"{output_dir}/valid.jsonl", 'w') as f:
            for ex in self.valid_examples:
                f.write(json.dumps(ex) + '\n')
                
    def evaluate_model(self, model, metrics=['bleu', 'exact_match']):
        """Basic evaluation scaffold"""
        results = {
            'test': self._evaluate_split(self.test_examples, model, metrics),
            'valid': self._evaluate_split(self.valid_examples, model, metrics)
        }
        return results
    
    def _evaluate_split(self, examples: List[Dict], model, metrics: List[str]):
        results = {}
        
        predictions = []
        references = []
        
        for ex in examples:
            # Get model prediction
            input_text = ex['informal_prefix']
            pred = model.generate(input_text)
            predictions.append(pred)
            references.append(ex['formal_statement'])
            
        # Calculate metrics
        if 'bleu' in metrics:
            results['bleu'] = self._calculate_bleu(predictions, references)
        if 'exact_match' in metrics:
            results['exact_match'] = self._calculate_exact_match(predictions, references)
            
        return results
    
    def _calculate_bleu(self, preds, refs):
        # Add BLEU calculation
        return 0.0
        
    def _calculate_exact_match(self, preds, refs):
        matches = sum(1 for p, r in zip(preds, refs) if p.strip() == r.strip())
        return matches / len(preds)

# Example usage:
dataset = ProofNetDataset('./lean_project/ProofNet/proofnet.jsonl')
dataset.save_splits('./lean_project/ProofNet')

# Example evaluation
class DummyModel:
    def generate(self, input_text):
        return "dummy prediction"
        
model = DummyModel()
results = dataset.evaluate_model(model)
print(results)
