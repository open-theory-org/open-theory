import Models.QuantizedMLP.Basic
import Models.Exact.MLP

/-!
# A quantized MLP is a ReLU network built from exact primitives

`QuantizedMLP` stores a one-hidden-layer integer ReLU network as a list of 2-bit codes. Read as
parameters of `Exact.reluMLP d [h] c` (two `linear` layers around a `relu`), its scores are that
network's integer forward pass (`scoresOfWeights_eq_run`). So the quantized MLPs are members of the
ReLU-network family: every fact proved once for `Exact.Net` (agreement with TorchLean, interval
soundness) applies to them.
-/

namespace OpenTheory.QuantizedMLP

/-- The network: `inputs → hidden` linear, ReLU, `hidden → classes` linear. -/
def asNet (a : Arch) : Exact.Net a.inputs a.classes := Exact.reluMLP a.inputs [a.hidden] a.classes

/-- The weights in storage order as the network's parameters, the biases scaled. -/
def netParams (a : Arch) (ws : List ℤ) : (asNet a).Params :=
  let rest := ws.drop (a.inputs * a.hidden)
  let out := rest.drop a.hidden
  (((rows a.inputs a.hidden ws, (rest.take a.hidden).map (a.hiddenBiasScale * ·)), ()),
    (rows a.hidden a.classes out, ((out.drop (a.hidden * a.classes)).take a.classes).map (a.outputBiasScale * ·)))

theorem dot_eq (r x : List ℤ) : dot r x = Exact.dot r x := rfl

/-- **The scores are the network's forward pass.** -/
theorem scoresOfWeights_eq_run (a : Arch) (ws x : List ℤ) :
    scoresOfWeights a ws x = (asNet a).run (netParams a ws) x := by
  simp only [scoresOfWeights, asNet, netParams, Exact.reluMLP, Exact.linearReLU, Exact.Net.run,
    Exact.linear, Exact.relu, Exact.linearRun, dot_eq, List.zipWith_map_right, List.map_zipWith]
  simp only [max_comm (0 : ℤ)]

/-- The code's network and parameters. -/
theorem logits_eq_run (a : Arch) (code : Code a.parameterCount 4) (x : List ℤ) :
    logits a code x = (asNet a).run (netParams a (weights code)) x :=
  scoresOfWeights_eq_run a (weights code) x

end OpenTheory.QuantizedMLP
