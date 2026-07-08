import os
import re

def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    # Find _\mathfrak and replace with _{\mathfrak <nextchar>}
    # We can match _\mathfrak followed by optional spaces and a character
    def repl(m):
        return r"_{\mathfrak{" + m.group(1) + r"}}"

    new_content = re.sub(r'_\s*\\mathfrak\s*([a-zA-Z])', repl, content)
    
    if new_content != content:
        with open(filepath, 'w') as f:
            f.write(new_content)
        print(f"Fixed {filepath}")

for root, _, files in os.walk('src/chapters'):
    for file in files:
        if file.endswith('.tex'):
            fix_file(os.path.join(root, file))
