#!/usr/bin/env python3
#
# update README from src/lib.rs. This does the same thing as `cargo readme`,
# except it converts rustdoc-style links that GitHub markdown doesn't
# understand to plain `code` style.
import re

with open('src/lib.rs') as f:
  doc = f.read()

doc = re.sub(r'^/\*!\n(.*)\*/.*$', r'\1', doc, flags=re.DOTALL)

doc = re.sub(r'\n\n```\n', r'\n\n```rust\n', doc)

# github doesn't understand [`rust_token`], but make sure [`name`](url) still works
doc = re.sub(r'\[(`[^`]*`)]\[[^]]*\]', r'\1', doc)
doc = re.sub(r'\[(`[^`]*`)](?!\()', r'\1', doc)

# increase header levels
doc = re.sub(r'^(#+)', r'#\1', doc, flags=re.M)

doc = """# genrc

[![Crates.io](https://img.shields.io/crates/v/genrc.svg)](https://crates.io/crates/genrc)
![MIT/Apache](https://img.shields.io/badge/license-MIT%2FApache-blue.svg)

""" + doc + """
## License

genrc is licensed under either the MIT or Apache 2.0 license, whichever you
prefer.
"""

with open('README.md', 'w', newline='\n') as f:
  print(doc, end='', file=f)
