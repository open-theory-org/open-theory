# Audit notes (A=substantive real, B=real but basic/infra, C=toy scalar formula, D=hollow: assumed conclusion / Bool flags / bundle)
## OpenTheory
Data/* B infra (Population, IIDSample, Dataset) KEEP
Parameterization/MuP,NTK B-thin (structs + trivial positivity)
EndToEnd D (population_risk_le_sum = linarith on assumed parts; compiler Bool/rfl; "unification" bundles)
Representation/Alignment B real (projector alignment, Frobenius)
Representation/Features,Gram B infra
Representation/FeatureLearningAdvantage A- real 2-layer one-step preact shift + 1D ridge MSE; single input
Representation/CanonicalTaskRepresentation C mostly (CE=margin identity real; quotient trivial; irrep cost invented formula)
Representation/HilbertSuperposition B/D (interference coherence bound real-basic; RLVR verifier assumes V*(y-ŷ)=0)
Representation/InterpretabilityAndControlDuality C/D
Representation/OpenWorldCausalDiscovery C/D
Architectures/Attention A- real masked softmax attention: weights, convex hull, norm & value-perturbation bounds (TorchLean spec)
Architectures/AttentionAblation A- real head-ablation bounds, multilayer residual perturbation, population MSE after ablation
Architectures/AttentionLogitStability A- real score-perturbation L1, focused/margin -> output stability
Architectures/Basic,Residual,Torch,Transformer B infra (Torch MLP Lipschitz real; Transformer = config wrapper)
Architectures/CompositionalNetworkCalculus D (struct of numbers, invented "risk")
Architectures/ConvolutionalGeneralization A-/overclaim: shift equivariance, 1-layer CNN param-Lipschitz, covering tail real; "CNN beats MLP sample complexity" compares upper bounds only
Architectures/DeepCompositionalHierarchy C (invented formulas, L*d<d^L)
Architectures/Expressivity B mixed (subspace lift, interpolation w/ anchor real; exists_subspace_approximation ASSUMES realizability, NonPolynomial unused)
Architectures/GatedDeltaHybridAtlas B(Hilbert delta-rule erasure) + C/D
Architectures/HilbertMLAAndDistributionSpeculative A- speculative sampling emits target PMF exactly (finite vocab) real; projection Pythagoras B
Architectures/InContextAlgorithmEmergence C
Architectures/InContextRetrieval B real softmax margin lemmas; margin growth per step ASSUMED (except bilinear query step)
Architectures/InductionHeadDynamics C+ toy (m identical distractors) but correct softmax vs linear-attention comparison
Architectures/LongContextAndFastInference C/D (FLOP formulas; "KL distortion" defined := 0)
Architectures/OptimalControlRegimes C/D ; RoutingAndMoEOptimality C/D ; RuntimeReasoningGuardrail C
Architectures/SpectralSparseCircuit B (equivariance/bulk invariance real) + C/D ("optimal" = smaller param count in invented risk p*c/n)
Dynamics/Contraction B (resnet step Lipschitz real) but resnet_representation_contraction is trivial ∃ (D)
Dynamics/CoupledTrainingDynamics C
Dynamics/DeepResidualScaling A- real deep residual Lipschitz/norm window, (1+c/L)^L<=e^c
Dynamics/EarlyTrajectoryIdentifiabilityAndWSD C/D (3-point identification of an ASSUMED geometric curve; WSD dispatch)
Dynamics/FeatureAlignment C/D (decay hypothesis assumed; feature_learning_resnet_alignment = trivial ∃ overlap≥1-ε)
Dynamics/FeatureStep A real exact gradient of 2-layer net; NTK/muP/feature-learning one-step preactivation rates
Dynamics/TangentStep A real tangent-gap bounds per parameterization
Dynamics/GradientSpectralEmergence B real eigenmode dynamics of LINEAR update w+ηcGw
Dynamics/GrokkingPhaseTransition C/D ; HierarchicalMultiIndex C (scalar recurrence α+ηcα^s toy, correct) ; MorseCanonicalization C/D ; CoupledTraining C
Dynamics/MLP{BatchBounds,BatchTrajectory,Comparison,Contractive,Endpoint,LocalSharpness,Residual,Trajectory} A — STRONGEST CORE: actual nonlinear 2-layer GD (single + batch), linearization gap, contractive horizon-free envelopes, endpoint=ridge, local-sharpness descent & grad-norm bound
Dynamics/MultiStepSpectralBias B- (signal/bulk exponential growth ASSUMED as hypotheses; alignment follows)
Dynamics/SpectralBias B-/D (spectral_bias_mup_alignment trivial ∃)
Generalization/FiniteClass,FiniteLearning A real Hoeffding+union, ERM/approx-ERM tail (via StatLean)  <-- directly usable for held-out model selection
Generalization/Covering A real cover->uniform deviation tail, compact cover, approx learner tail
Generalization/BallCover A- real ε-net of Euclidean ball (card (⌈2R√d/δ⌉+1)^d — exponential, loose)
Generalization/RidgeRisk A real fixed-design ridge risk, df ≤ rank, GD→ridge
Generalization/KernelRidge A real primal/dual, kernel smoother, rank
Generalization/TrainedRidge A real GD iterate excess-risk tail (linear)
Generalization/PredictionGap A ; PopulationBounds A- ; AttentionRisk B ; StatisticalBridge B infra
Generalization/MLPRisk A (single input) ; MLPFixedDesign A- ; MLPBatchRisk A (multi-input FIXED DESIGN trained 2-layer net expected MSE)
Generalization/TrajectoryGeneralization A- real: 2-layer first-layer param cover + tail; contractive GD trajectory stays in ball -> population tail. Best NN generalization result in repo; numerically vacuous (cover exp in m*d)
Generalization/TransformerGeneralization B: generic Lipschitz-in-params cover tail (hmodel global Lipschitz — false for real multi-layer nets), residual-stack perturbation real; ICL end-to-end D (margins assumed); safety ablation bounds B
Generalization/Rademacher B deterministic sign-avg lemmas; rademacher_symmetrization = trivial ∃C≤2 (D). No actual Rademacher complexity bound.
Generalization/OperatorNorm B deterministic Frobenius bounds; gaussian_operator_norm_bound trivial ∃ (D); "RandomInit_expectation" misnamed (no probability)
Generalization/Bounds B infra
Generalization/SpikedSampleComplexity C (spiked MSE formula DEFINED, not derived; few real alignment bridges)
Generalization/AutoregressiveOOD C ; TestTimeScaling C (p^K, assumed scaling law) ; ComputeOptimalSynthesis C (Chinchilla form assumed; calculus correct)
Generalization/MinimaxStatisticalUnimprovability C overclaim (minimax over a scalar family only)
Generalization/{AuditableSmallModelDominance,DataCurriculumAndTokenSelection,DistillationAndSelfPlayRLVR,OptimalGeneralizationRegimes,PredictiveModelPrescription,UniversalAdaptationCalculus,UniversalPredictionAtlas,UniversalTaskTaxonomy,ZeroShotCompiler} C/D
Optimization/Ridge A real linear ridge: gradient, strong monotone, GD convergence, radius
Optimization/FiniteRidge A real dataset ridge, uniform step for bounded rows
Optimization/Convergence B conditional (risk exp approach GIVEN rate hypothesis on derivative)
Optimization/LocalSharpnessDescent B+ (descent lemma given quadratic upper bound; MLP coercive norm bounds real)
Optimization/JointPLConvergence B+ conditional: real 2-layer GD convergence to zero loss BUT Jacobian coercivity assumed ∀t along trajectory (the hard part)
Optimization/MomentumAdamTrajectory B (EMA/bias-correction algebra, AdamW stays in ball real; adamw_mlp_generalization_tail real via cover; per-coordinate "noise penalty" model C)
Optimization/OperatorNewtonSchulzAndNoiseScale B real (NS fixed points, orthogonal equivariance, scalar cubic convergence; minibatch variance under ORTHOGONAL noise assumption)
Optimization/PreconditionedDescent B conditional (diag precond/signGD descent given assumed coordinate quadratic bound)
Optimization/StochasticSharpnessSGD C+/B- (no randomness; deterministic recurrence with σ²/B plugged in; noise-ball lemma)
Optimization/Optimizers B infra (TorchLean SGD/Adam bridge)
Optimization/GlobalSaddlePL C (PL-from-Gram given margin; saddle variance toy recurrence; two-phase convergence assumes both phases)
Optimization/{CertiRPM,ResidualPreconditionedMomentum} C (per-coordinate quadratic progress model; regret identities)
Optimization/PullbackFisherAndMorseTheory C (1D/diagonal quadratic Fisher merge, Schur-complement pruning algebra correct; rest C/D)
Optimization/{AlgorithmicOptimizerUnimprovability,DistributedClusterScaling,EdgeOfStabilityFlatness,FastestTrainingAndRoofline,MatrixSpectralPreconditioning,OptimalTrainingRegimes,VerifiableSelfImprovement,WienerSpectralOptimizerAtlas} C/D (defs like minWork:=p; "PAC-Bayes" formula invented; Bool dispatch)
Certification/* (21 files) D: finance/macro scalar formulas, JSON telemetry "compilers", Bool optimal flags proved by rfl/decide, default telemetry examples. ZeroKnowledgeCommitment: "Pedersen" = g*w+h*r in a ring (not a group exponent) -> algebraic sigma-protocol identities true but ZERO cryptographic security; AgentZeroKnowledgePassport same. ProofCarryingAI C (scalar rollout barrier).
## OpenEconomics
