"""Check that every Lean name cited in the blueprint (`\\lean{...}`) is a declaration.

usage: python3 check_blueprint_decls.py LEAN_DECLS DECL_JSON

LEAN_DECLS is `blueprint/lean_decls`, written by `leanblueprint web`. DECL_JSON is
`docs/declarations/declaration-data.bmp` from the API documentation built by doc-gen4.
"""
import json
import sys

lean_decls, decl_path = sys.argv[1:3]
decls = json.load(open(decl_path))["declarations"]
names = [line.strip() for line in open(lean_decls) if line.strip()]
missing = [n for n in names if n not in decls]
for n in missing:
    print(f"error: the blueprint cites `{n}`, which is not a declaration")
print(f"{len(names) - len(missing)} of {len(names)} blueprint declarations found")
sys.exit(1 if missing else 0)
