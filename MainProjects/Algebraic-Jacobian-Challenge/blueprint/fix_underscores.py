import os
import re

def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    # Find all \texttt{...} and replace unescaped _ with \_
    def replace_underscores(match):
        inner_text = match.group(1)
        # We need to replace _ with \_, but only if it's not already escaped.
        # It's easier to just replace all `\_` with `_`, then replace all `_` with `\_`
        inner_text = inner_text.replace(r'\_', '_')
        inner_text = inner_text.replace('_', r'\_')
        return r'\texttt{' + inner_text + '}'

    new_content = re.sub(r'\\texttt{([^{}]*)}', replace_underscores, content)
    
    # We might have nested braces, but usually \texttt{} doesn't have them or we can just fix the ones that broke.
    # Let's see if content changed
    if new_content != content:
        with open(filepath, 'w') as f:
            f.write(new_content)
        print(f"Fixed {filepath}")

for root, _, files in os.walk('src/chapters'):
    for file in files:
        if file.endswith('.tex'):
            fix_file(os.path.join(root, file))
