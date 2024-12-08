import openai
import chromadb
from pathlib import Path
from tqdm import tqdm
import os

class MathlibVectorDB:
    def __init__(self, 
                 clean_mathlib_path: str,
                 persist_directory: str,
                 collection_name: str = "mathlib"):
        self.path = Path(clean_mathlib_path)
        self.client = chromadb.PersistentClient(path=persist_directory)
        # Get existing collection or create new one
        try:
            self.collection = self.client.get_collection(name=collection_name)
            print(f"Using existing collection: {collection_name}")
        except:
            self.collection = self.client.create_collection(name=collection_name)
            print(f"Created new collection: {collection_name}")

        # Set OpenAI key
        if not os.environ.get("OPENAI_API_KEY"):
            raise ValueError("OPENAI_API_KEY not found in environment variables")
        openai.api_key = os.environ["OPENAI_API_KEY"]
        
    def create_embeddings(self, texts: list[str]) -> list:
        """Create embeddings using text-embedding-3-large"""
        response = openai.Embedding.create(
            model="text-embedding-3-large",
            input=texts
        )
        return [item["embedding"] for item in response["data"]]
        
    def create_database(self):
        # Collect all files
        files = list(self.path.glob("*.lean"))
        texts = []
        metadatas = []
        ids = []
        
        print(f"Reading {len(files)} files...")
        # Read file contents
        for file_path in tqdm(files, desc="Reading files"):
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                texts.append(content)
                metadatas.append({
                    "filename": file_path.name,
                    "size": len(content)
                })
                ids.append(str(file_path.stem))
        
        print("Generating embeddings (this might take a while)...")
        embeddings = self.create_embeddings(texts)
        
        print("Storing in ChromaDB...")
        # Store in vector DB
        self.collection.add(
            embeddings=embeddings,
            documents=texts,
            metadatas=metadatas,
            ids=ids
        )
        
        print(f"Created database with {len(files)} files")
        return self.collection

# Usage
db_creator = MathlibVectorDB(
    clean_mathlib_path="./lean_project/LeanProject/CleanMathlib",
    persist_directory="./vector_db_large"
)
vector_db = db_creator.create_database()
