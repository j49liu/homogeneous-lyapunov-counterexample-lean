import HomogeneousObstruction.ForwardCompleteness

/-!
# Main theorem item (1)

The manuscript concludes the Lyapunov analysis by Lyapunov's direct method.
`ForwardCompleteness.lean` supplies the standard continuation step that is
not packaged in mathlib, while `LyapunovGAS.lean` supplies the textbook
epsilon--delta stability and attraction argument.  This module composes them
for the explicit cubic field.
-/

namespace HomogeneousObstruction

noncomputable section

/-- Main theorem item (1): the origin of the explicit cubic vector field is
globally asymptotically stable.  The predicate uses the manuscript's
Euclidean norm and explicitly includes forward completeness. -/
theorem mainTheorem_item1 : GloballyAsymptoticallyStable fieldValue 0 :=
  globallyAsymptoticallyStable_fieldValue_of_forwardComplete forwardComplete_fieldValue

end

end HomogeneousObstruction
