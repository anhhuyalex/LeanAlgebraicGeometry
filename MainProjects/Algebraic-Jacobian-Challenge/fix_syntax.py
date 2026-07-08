import re

with open('AlgebraicJacobian/Picard/Pic0AbelianVariety.lean', 'r') as f:
    content = f.read()

# Fix docstring splits: move the helper lemmas BEFORE the docstring.
# For universallyClosed:
def move_helpers_before_docstring(theorem_name, helper_marker):
    global content
    # Find where the helper lemmas start
    idx = content.find(helper_marker)
    if idx == -1: return
    # Find the end of the helper lemmas
    end_idx = content.find("theorem " + theorem_name, idx)
    if end_idx == -1: return
    
    helpers = content[idx:end_idx]
    
    # We need to find the docstring that belongs to the theorem
    # The docstring is right before `idx`
    # Let's just remove the helpers from there, and put them before the docstring
    # The docstring starts with `/--`
    r_idx = content.rfind("/--", 0, idx)
    
    # Check if there are other things between r_idx and idx
    if r_idx != -1:
        # Move helpers to before r_idx
        content = content[:r_idx] + helpers + "\n" + content[r_idx:idx] + content[end_idx:]

move_helpers_before_docstring("universallyClosed", "/-! ### Helper Lemmas for `universallyClosed` -/")
move_helpers_before_docstring("smoothAtIdentity", "/-! ### Helper Lemmas for `smoothAtIdentity` -/")
move_helpers_before_docstring("smooth_of_smoothAtIdentity", "/-! ### Helper Lemmas for `smooth_of_smoothAtIdentity` -/")

# Change `/-!` to `--` to avoid module docstring errors
content = content.replace("/-! ### Helper Lemmas", "-- ### Helper Lemmas")

# Fix `baseChangeAlgClosure (Pic0Scheme C).left).hom` to `baseChangeAlgClosure (Pic0Scheme C).left`?
# Or just remove `.hom`. 
# Wait, UniversallyClosed is a property of morphisms. 
# Let's change `baseChangeAlgClosure (X : Scheme)` to `baseChangeAlgClosure {k} (C : Over (Spec (.of k))) : Over (Spec (.of (kBar k)))`
content = content.replace("opaque baseChangeAlgClosure (X : Scheme) {k : Type u} [Field k] : Scheme",
                          "opaque baseChangeAlgClosure {k : Type u} [Field k] (C : Over (Spec (.of k))) : Over (Spec (.of (kBar k)))")

content = content.replace("baseChangeAlgClosure (Pic0Scheme C).left).hom", "baseChangeAlgClosure (Pic0Scheme C)).hom")
content = content.replace("baseChangeAlgClosure (Pic0Scheme C).left", "(baseChangeAlgClosure (Pic0Scheme C)).left")

# Fix schemePoints scope / implicit args
content = content.replace("opaque schemePoints (X : Scheme) (R : CommRingCat) : AddCommGroup", 
                          "opaque schemePoints (X : Scheme) (R : CommRingCat) : AddCommGroup")

# For SmoothOfRelativeDimension etc, Lean sometimes complains if they are implicit.
# Wait, the `schemePoints` error: "Note: It is not possible to treat `schemePoints` as an implicitly bound variable here".
# This means `schemePoints` wasn't found at all! Why?
# Did I put `opaque schemePoints` inside a section that was closed?
# Let's just make sure `schemePoints` is defined.

with open('AlgebraicJacobian/Picard/Pic0AbelianVariety.lean', 'w') as f:
    f.write(content)
