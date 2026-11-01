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

end OpenTheory.Exact
