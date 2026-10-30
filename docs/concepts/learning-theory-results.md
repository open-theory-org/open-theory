# Learning-theory results: what is proved and what is not

Moved from the README on 2026-10-27. Paths updated to `formal/`.

The implemented reuse slice uses pinned Mathlib and TorchLean: generic datasets
and population laws, finite-dimensional ridge regression with exact-GD bounds,
biased ReLU MLP/residual Lipschitz bounds, exact masked attention bounds,
masked/causal transformer inference, finite-second-moment population-risk envelopes,
and upstream SGD/momentum/Adam/AdamW state machines. Risk envelopes are not
generalization-gap or transformer-training guarantees. A narrow FoML subset now
supplies a conditional empirical-risk oracle bridge; its high-probability
generalization modules did not port directly. A narrow StatLean subset supplies
the first checked high-probability finite-class bound. Continuous neural-class
generalization remains the next statistical target.
Finite-model selection now has a proved empirical minimizer and an excess-risk
tail bound, including an approximate-selection variant; see
[`FiniteLearning.lean`](../../formal/core/LearningTheory/Generalization/FiniteLearning.lean).
[`Covering.lean`](../../formal/core/LearningTheory/Generalization/Covering.lean) extends that statistical
route to continuous classes with finite uniform loss covers, including an
approximate-learner excess-risk bound. Compactness supplies cover existence,
not a numerical cardinality estimate. Bounded-label ridge training now has a
sample-independent parameter-radius bound for every zero-initialized GD iterate.
[`TrainedRidge.lean`](../../formal/core/LearningTheory/Generalization/TrainedRidge.lean) combines that
radius, a step legal for every input bound `B`, a grid cover of the training
ball, and the finite-class tail. The loss is squared error normalized by
`(2RB+T)²`. The excess budget pays the optimization gap and the comparator's
regularization. The grid bound is not sharp, and the result is linear ridge
regression, not a neural-network guarantee.
[`RidgeRisk.lean`](../../formal/core/LearningTheory/Generalization/RidgeRisk.lean) is the informative
companion: with the design held fixed and white label noise of scale `σ`, the
ridge solution that exact gradient descent approaches has in-sample mean squared
error at most `(λ/4)‖θ*‖² + σ² df / m`. The degrees of freedom are at most the
rank of the design, hence at most `min(d, m)`, and a rank-`r` design replaces
`df` by `r`. A zero design has degrees of freedom zero even when the parameter
dimension is positive. The bias term is the regularization price and does not
shrink with the number of rows. This is the classical fixed-design
bias–variance shape, not a random-design generalization theorem and not a
neural-network theorem. It is the linear prototype of a kernel or NTK guarantee.
An MLP parameter-ball grid cover is exponential in the number of weights and
does not see this spectrum.
[`KernelRidge.lean`](../../formal/core/LearningTheory/Generalization/KernelRidge.lean) puts the same
bound on the kernel Gram `K = c A A*`. Gradient descent still trains the primal
parameter, and its predictions equal the smoother `K(K+λI)⁻¹`. Equal kernels
give equal predictions, and the rank of `K` equals the rank of the feature map.
This is the classical primal–dual identity. A frozen feature map inherits it.
It does not prove that a network stays near its linearization.
[`FeatureStep.lean`](../../formal/core/LearningTheory/Dynamics/FeatureStep.lean) is the one-step
comparison that separates those regimes for a two-layer network. On the loss
`(1/2)(f(x)-y)²`, one gradient step changes hidden preactivation `i` by
`-η₁ (f(x)-y) σ'(preᵢ) W₂ᵢ ‖x‖²`. With the readout at most its initialization
scale, the checked NTK rate moves that preactivation by `O(1/√m)` and the
checked μP rate moves it by `O(1/m)`. Both vanish as the width grows. The
first-layer rate `η₁ = m`, with a readout coordinate of size `1/m`, moves it by
a width-independent amount. This is the one-step calculation behind the
feature-learning exponent. It is not an infinite-width limit and not a
generalization bound.
[`TangentStep.lean`](../../formal/core/LearningTheory/Dynamics/TangentStep.lean) compares that step
with its tangent update. If the activation derivative is `M`-Lipschitz, the
output gap is at most `M |f(x)-y|² L² ‖x‖⁴ / √m` for the checked NTK rate and
the same quantity over `m²` for the checked μP rate. The feature-learning rate
leaves a gap of order `|f(x)-y|²`.
[`PredictionGap.lean`](../../formal/core/LearningTheory/Generalization/PredictionGap.lean) says a
predictor within `δ` of the ridge predictor has in-sample mean squared error
at most twice the ridge bound plus `2δ²/m`. That `δ` is not yet the tangent
gap: the tangent theorem compares the network with one tangent step, not with
the ridge solution.
See [dependency status](../architecture/dependency-status.md) for tested
imports and libraries still awaiting integration. The axiom audit rejects `sorryAx`
in every OpenTheory declaration not listed as an open target.
