import os

# --- Configuration ---
try:
    start_path = os.path.dirname(os.path.abspath(__file__))
except NameError:
    start_path = os.getcwd()

# Define the output file name
output_file = os.path.join(start_path, "directory_tree.txt")

# List of directories to completely ignore.
ignored_dirs = {'__pycache__', '.git', '.vscode', '.idea', 'runs'}

# --- Script Logic (ASCII-Safe) ---
def create_directory_tree_safe(startpath, file_handle):
    """
    Generates a visual directory tree structure using only basic ASCII characters
    and writes it to the provided file handle.
    """
    file_handle.write(f"--- Project Structure for: {startpath} ---\n\n")
    
    for root, dirs, files in os.walk(startpath, topdown=True):
        # In-place modification of dirs to prune the walk
        dirs[:] = [d for d in sorted(dirs) if d not in ignored_dirs]
        
        level = root.replace(startpath, '').count(os.sep)
        
        # ASCII-safe indentation
        indent = '|   ' * (level - 1) + '+-- ' if level > 0 else ''
        
        # Write the current directory name
        file_handle.write(f'{indent}{os.path.basename(root) or start_path}/\n')
        
        # ASCII-safe sub-indentation for files
        sub_indent = '|   ' * level
        
        # Combine and sort all items for consistent output
        all_items = sorted(dirs + files)
        
        for i, name in enumerate(all_items):
            is_last = (i == len(all_items) - 1)
            
            # ASCII-safe prefixes
            connector = 'L-- ' if is_last else '+-- '
            
            if name in files:
                file_handle.write(f'{sub_indent}{connector}{name}\n')

if __name__ == "__main__":
    # Open the file for writing
    with open(output_file, 'w', encoding='utf-8') as f:
        create_directory_tree_safe(start_path, f)
        f.write("\n--- End of list ---\n")
    
    print(f"Directory tree saved to: {output_file}")