import Models.Exact.Basic
import Properties.Prediction
import Properties.Interface

/-!
# ReLU networks provide a decision

A network `g` with parameters `θ` decides the class its scores rank strictly first (`Predicts`);
the property `Decides` of `Properties/Interface.lean` applies to it as it is.
-/

open TorchLean

namespace OpenTheory.Exact

instance {m k : ℕ} (g : Net m k) : HasDecision g.Params (Tensor ℝ [m]) (Fin k) :=
  ⟨fun θ x c => Predicts (g.eval θ x) c⟩

/-- **`exact-output`.** The network's integer forward pass on `x` is exactly `y`. -/
def Net.OutputIs {m k : ℕ} (g : Net m k) (y : List ℤ) : Property g.Params (List ℤ) :=
  fun θ x => g.run θ x = y

end OpenTheory.Exact
