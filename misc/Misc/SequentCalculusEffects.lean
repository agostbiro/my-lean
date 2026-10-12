/-!
# Effects in a sequent calculus

  Minimal demo: effects in a sequent calculus, in Lean 4 (core only, no Mathlib).

  Goal:
    Demonstrate a small proof system for safety against arbitrary controller
    strategies, show that effect rows bound controller influence, and
    illustrate how an interlock replaces a behavioral assumption with an
    enforced invariant.

    Here, "untrusted" is a modeling choice: Γ imposes no restriction on a
    role's answers, so every strategy of type (Obs A)* → Action A is allowed.
    Lean checks the consequences of this definition. It does not establish
    that the chosen observations, actions and interactions capture every
    relevant real-world attacker capability.

    The demo establishes three results:

    1. Derivation → robustness modality (`sound`).
       The sequent rule for `ask` requires a proof for every answer that Γ
       permits. A derivation therefore proves □_Γ φ: the final property φ
       holds for every permitted strategy, including ones that use history.

    2. Effect row → bound on influence (`irrelevant_of_not_mem`).
       Starting from a strategy profile that respects Γ, changing only a
       role outside E cannot change the result, with initial histories fixed.
       E is an information-flow label in this limited sense. There is no
       confidentiality policy or model of what an external observer can see.

    3. Assumed constraints → enforced invariant
       (`raw_deriv`, `raw_not_robust`, `guarded_robust`).
       The raw reactor loop preserves safety when Γ excludes two unsafe
       commands. Removing those restrictions admits a counterexample.
       A trusted interlock preserves safety for every modeled strategy,
       from any safe initial state and for any finite number of steps.

    These guarantees are related but distinct. The effect row tracks possible
    influence on the result; the modality states robustness of a particular
    property. The computer can change the guarded reactor's final valve
    positions while every outcome remains safe (`guarded_influenced`).
    Conversely, a role can be asked by the protocol yet have no influence,
    because Γ rules out the paths that ask it (`operator_irrelevant`,
    `operator_matters`). No equivalence between effects, the modality and
    information-flow labels is proved here.

  Connection to STPA:
    The example uses Unsafe Control Actions (UCAs) from STPA (System-Theoretic
    Process Analysis). Ordinary STPA already investigates why UCAs can occur,
    including controller flaws, incorrect feedback and actuator failures.
    The comparison here is between assuming behavioral constraints and
    enforcing them despite arbitrary controller behavior. It does not
    identify those cases with STPA and STPA-Sec (STPA for Security).
    The counterexample exhibits a hazardous behavior; it does not explain
    its cause or perform a full STPA Step 2 causal analysis.

  Strategy vs strategy space:
    A strategy is one possible behavior, whether benign, faulty or malicious.
    Robustness quantifies over the whole permitted strategy space; it does
    not require enumerating attacks. `raw_not_robust` supplies one concrete
    strategy as a counterexample to the raw loop's robustness.

    Capabilities are bounded jointly by the types and the protocol: `State`
    describes observations, `Cmd` describes actions, and `Protocol` fixes which
    roles are asked and how their answers are used. Γ adds restrictions on
    answers within that language. It can fix a command per observation,
    exclude some commands (`noUCA`), or allow every command (`untrusted`).

    For background on a systems-theoretic approach to safety and security,
    see Young & Leveson,
    "An Integrated Approach to Safety and Security Based on Systems Theory",
    CACM 57(2), 2014:
    https://cacm.acm.org/opinion/an-integrated-approach-to-safety-and-security-based-on-systems-theory/

  Judgment:   Γ ⊢ P : φ ! E
    Γ  = behavioral assumptions: which answers each role is permitted to give
    P  = protocol (a tree of `ask` effects)
    φ  = property of the final state
    E  = effect row: an upper bound on roles P may ask under Γ

  Example: a simplified chemical reactor based on the MIT STPA slides.
  Hazard H = "catalyst valve open while water valve closed".
  Source: N. Leveson, MIT 16.63J System Safety (Spring 2016), Session 10,
    "Systems Theoretic Process Analysis (STPA) Intro, Basic Components",
    slides 33–34 (causal analysis) and 36–56 (reactor). MIT OpenCourseWare:
    https://ocw.mit.edu/courses/16-63j-system-safety-spring-2016/resources/mit16_63js16_lecnotes10/

  Components, by section:

    1. Syntax.
       `Role`, `State` and `Cmd` are the controllers, the valve state and the
       commands. A `Protocol` has two forms: `ret s` ends with the state `s`,
       and `ask A o k` shows the observation `o` to role `A` and continues
       with `k` applied to the answer.

    2. Semantics.
       A `Strategy` gives the answer of each role from its observation
       history. `run` executes a protocol with a strategy and returns the
       final state. `Assumptions` is the type of Γ. `Satisfiable` says that
       Γ always permits some answer, `Respects` says that a strategy stays
       inside Γ, and `Box` is the modality □_Γ φ.

    3. Sequent calculus.
       `Deriv` is the judgment Γ ⊢ P : φ ! E, with one rule for `ret` and
       one for `ask`. `Effects` is the same judgment with a trivial φ, so
       it states the effect row only.

    4. Metatheory.
       `sound` turns a derivation into `Box`. `irrelevant_of_not_mem` shows
       that a role outside E cannot change the result.

    5. Reactor example.
       `hazard` and `safe` define the property. `apply` gives the effect of
       a command, `isUCA` marks the two unsafe commands, and `interlock`
       replaces them with `skip`. `loop` asks the computer n times;
       `rawLoop` sends each answer to the valves, and `guardedLoop` sends it
       through the interlock first. The choices of Γ are `untrusted`,
       `noUCA`, and `operatorNoUCA`, which restricts only the operator.
       `escalate` is a one-step protocol that sends each UCA request to the
       operator. The theorems of results 1 to 3 above follow, and
       `escalate_robust` shows safety with an untrusted computer. The
       section ends with five concrete proof trees, each drawn above its
       Lean term.

    6. Limits of this demo.

  How the components connect:

      P : Protocol -------+
                          | run
      h : Strategy -------+------> final state : State
          ^                            |
          | Respects                   | φ holds for every h
          |                            | that respects Γ
      Γ : Assumptions                  v
                                   Box Γ φ P
                                       ^
                                       | sound
      Deriv Γ E φ P -------------------+
          |
          | Deriv.effects
          v
      Effects Γ E P -- irrelevant_of_not_mem --> a role outside E cannot
                                                 change the result of `run`

    The top half is the semantics (sections 1 and 2). The bottom half is the
    proof system (sections 3 and 4). In the example (section 5), `loop_deriv`
    builds the derivations `raw_deriv` (Γ = `noUCA`) and `guarded_deriv`
    (Γ = `untrusted`). `sound` then gives `guarded_robust`, and
    `irrelevant_of_not_mem` gives `operator_irrelevant`.

  See section 6 for the limits of this demo.
-/

namespace Misc.SequentCalculusEffects

/-! ## 1. Syntax: protocols with one effect, `ask` -/

/-- The roles (controllers) in the control structure. -/
inductive Role | computer | operator
  deriving DecidableEq, Repr

/-- The state of the reactor: the positions of the two valves. -/
structure State where
  /-- The water valve is open. -/
  water    : Bool
  /-- The catalyst valve is open. -/
  catalyst : Bool
  deriving DecidableEq, Repr

/-- The commands that a role can send to the valves. -/
inductive Cmd | openWater | closeWater | openCatalyst | closeCatalyst | skip
  deriving DecidableEq, Repr

/-- A protocol asks roles for commands. The continuation `k` receives the
    answer. The protocol does not say what the answer is: a handler supplies
    it.

    Letters used in this file:
    - `A`: the role that is asked.
    - `o`: the observation, the state shown to `A`.
    - `c`: a command, usually the answer of `A`.
    - `k`: the continuation, the rest of the protocol for each answer.
    - `s`: a state, such as the final state in `ret s`. -/
inductive Protocol where
  | ret : State → Protocol
  | ask : Role → State → (Cmd → Protocol) → Protocol

/-! ## 2. Semantics: handlers are strategies `Obs* → Action` -/

/-- A deterministic, total strategy for every role, using its own observation
    history. Each function describes a possible behavior of that role. -/
def Strategy := Role → List State → Cmd

/-- Run a protocol with a handler. `hist r` = what role `r` has observed so
    far. -/
def run (h : Strategy) (hist : Role → List State) : Protocol → State
  | .ret s => s
  | .ask A o k =>
    let hist' := fun r => if r = A then o :: hist r else hist r
    run h hist' (k (h A (hist' A)))

/-- Behavioral assumptions Γ: `Γ A o c` = "role A may answer c when it observes o".
    Allowing every command models an untrusted role; allowing exactly one per
    observation fixes a policy based only on the current observation. Γ adds
    restrictions within the capabilities provided by the types and protocol.
    `Box` below quantifies over every strategy that respects these restrictions.
    Γ should be `Satisfiable`: otherwise no strategy respects it. -/
def Assumptions := Role → State → Cmd → Prop

/-- Γ permits at least one command for every role and observation. -/
def Satisfiable (Γ : Assumptions) : Prop := ∀ A o, ∃ c, Γ A o c

/-- The strategy `h` stays inside Γ: every answer of every role is one that
    Γ permits for the current observation. This covers all roles, histories
    and observations, including ones that no run reaches. -/
def Respects (Γ : Assumptions) (h : Strategy) : Prop :=
  ∀ A hs o, Γ A o (h A (o :: hs))

/-- A satisfiable Γ is respected by some strategy, so `Box Γ` is not vacuous. -/
theorem Satisfiable.exists_respects {Γ : Assumptions} (hΓ : Satisfiable Γ) : ∃ h, Respects Γ h :=
  ⟨fun A hs => match hs with
    | []     => .skip
    | o :: _ => Classical.choose (hΓ A o),
   fun A _ o => Classical.choose_spec (hΓ A o)⟩

/-- The robustness modality □_Γ φ: the final state satisfies φ for every
    strategy that Γ permits and every initial history. If Γ is not
    `Satisfiable`, no strategy respects it and `Box Γ φ P` holds for every φ
    and P. -/
def Box (Γ : Assumptions) (φ : State → Prop) (P : Protocol) : Prop :=
  ∀ h, Respects Γ h → ∀ hist, φ (run h hist P)

/-! ## 3. The sequent calculus: two rules -/

/-- `Deriv Γ E φ P`  ≈  Γ ⊢ P : φ ! E

    Deriv Γ E φ P is the claim that a proof tree exists for the judgment Γ ⊢ P : φ ! E.

    ```
    Γ   ⊢   P : φ ! E
    |       |   |   +-- effect row: the roles that P can ask
    |       |   +------ property of the final state
    |       +---------- protocol
    +------------------ assumptions: the answers that each role can give
    ```

    The sequent says: if every role gives only answers that Γ permits, the
    protocol `P` ends in a state that satisfies φ. It also says that `P` asks
    only roles in E. -/
inductive Deriv (Γ : Assumptions) (E : List Role) (φ : State → Prop) : Protocol → Prop
  /-- ret:  φ s  ⟹  Γ ⊢ ret s : φ ! E -/
  | ret {s} : φ s → Deriv Γ E φ (.ret s)
  /-- ask (left rule for the effect): A ∈ E, and for every answer c that Γ permits,
      Γ ⊢ k c : φ ! E  ⟹  Γ ⊢ ask A o k : φ ! E

      ```
        A ∈ E      for each c with Γ A o c:  Γ ⊢ k c : φ ! E
       ------------------------------------------------------ ask
                      Γ ⊢ ask A o k : φ ! E
      ```

      The conclusion, below the line, is the sequent for the protocol that
      asks the role `A` and then continues with `k`. The first premise says
      that the effect row E permits a question to `A`. The second premise is
      the left-rule part: for each command `c` that Γ permits `A` to answer on
      the observation `o`, the sequent holds for the rest of the protocol
      `k c`. -/
  | ask {A o k} : A ∈ E → (∀ c, Γ A o c → Deriv Γ E φ (k c)) →
      Deriv Γ E φ (.ask A o k)

/-- `Effects Γ E P`  ≈  Γ ⊢ P ! E: the effect row alone, with no claim about
    the final state. -/
abbrev Effects (Γ : Assumptions) (E : List Role) : Protocol → Prop := Deriv Γ E (fun _ => True)

/-! ## 4. Metatheory -/

/-- A proof tree for the sequent Γ ⊢ P : φ ! E gives a proof tree for the same
    protocol with the same effect row and no claim about the final state. -/
theorem Deriv.effects {Γ E φ P} (d : Deriv Γ E φ P) : Effects Γ E P := by
  induction d with
  | ret _ => exact .ret trivial
  | ask hA _ ih => exact .ask hA ih

/-- Soundness: if the sequent Γ ⊢ P : φ ! E has a proof tree, then φ holds for
    the final state of `P` under every strategy that respects Γ. -/
theorem sound {Γ E φ P} (d : Deriv Γ E φ P) : Box Γ φ P := by
  intro h hR
  induction d with
  | ret hφ => intro _; exact hφ
  | @ask A o k _ _ ih =>
    intro hist
    simp only [run]
    apply ih
    have := hR A (hist A) o
    simpa using this

/-- Effect rows bound influence: if the role `B` is not in the effect row E of
    `P`, a change to the strategy of `B` alone does not change the final state
    of `P`.

    The name reads: `B` is irrelevant to the result, if `B` is not a member
    of E. "mem" is short for membership (`∈`), so `not_mem` is `hB : B ∉ E`.

    - The initial histories are the same in both runs.
    - Only `h'` must respect Γ. The replacement strategy of `B` in `h` has no
      restriction.
    - Only the effect judgment is used: apply `Deriv.effects` to a derivation. -/
theorem irrelevant_of_not_mem {Γ E P} (d : Effects Γ E P) (B : Role) (hB : B ∉ E)
    (h h' : Strategy) (hR' : Respects Γ h') (agree : ∀ r, r ≠ B → h r = h' r) :
    ∀ hist, run h hist P = run h' hist P := by
  induction d with
  | ret _ => intro _; rfl
  | @ask A o k hA _ ih =>
    intro hist
    have hne : A ≠ B := fun e => hB (e ▸ hA)
    simp only [run, agree A hne]
    exact ih _ (by simpa using hR' A (hist A) o) _

/-! ## 5. STPA-inspired example: chemical reactor -/

/-- Hazard H: the catalyst valve is open while the water valve is closed. -/
def hazard (s : State) : Bool := s.catalyst && !s.water

/-- A state is safe if it is not in the hazard. -/
def safe (s : State) : Prop := hazard s = false

/-- The effect of a command on the state. -/
def apply : Cmd → State → State
  | .openWater,     s => { s with water := true }
  | .closeWater,    s => { s with water := false }
  | .openCatalyst,  s => { s with catalyst := true }
  | .closeCatalyst, s => { s with catalyst := false }
  | .skip,          s => s

/-- The two modeled UCAs (Unsafe Control Actions): opening the catalyst valve
    while the water valve is closed, and closing the water valve while the
    catalyst valve is open. -/
def isUCA (s : State) : Cmd → Bool
  | .openCatalyst => !s.water
  | .closeWater   => s.catalyst
  | _             => false

/-- Trusted interlock: uses the actual valve state to block the two modeled UCAs. -/
def interlock (s : State) (c : Cmd) : Cmd := if isUCA s c then .skip else c

/-- `loop filter n s` is the protocol that starts in the state `s` and asks the
    computer for a command `n` times, with each command sent through `filter`
    before the valves get it. -/
def loop (filter : State → Cmd → Cmd) : Nat → State → Protocol
  | 0,     s => .ret s
  | n + 1, s => .ask .computer s (fun c => loop filter n (apply (filter s c) s))

/-- The control loop with no interlock: every command goes to the valves. -/
def rawLoop     := loop (fun _ c => c)

/-- The control loop with the interlock. -/
def guardedLoop := loop interlock

/-- No behavioral restrictions on any role. Every strategy in the chosen
    language respects these assumptions. The reactor loop asks only the
    computer. -/
def untrusted : Assumptions := fun _ _ _ => True

/-- Behavioral assumption: every role avoids the two modeled UCAs.
    This encodes constraints used by the example, not the STPA methodology. -/
def noUCA : Assumptions := fun _ s c => isUCA s c = false

/-- Mixed behavioral assumption: the operator avoids the two modeled UCAs, and
    the computer has no restriction. -/
def operatorNoUCA : Assumptions := fun r s c => r = .operator → isUCA s c = false

/-! ### Proofs -/

theorem untrusted_satisfiable : Satisfiable untrusted := fun _ _ => ⟨.skip, trivial⟩

theorem noUCA_satisfiable : Satisfiable noUCA := fun _ _ => ⟨.skip, rfl⟩

theorem operatorNoUCA_satisfiable : Satisfiable operatorNoUCA :=
  fun _ _ => ⟨.skip, fun _ => rfl⟩

/-- Some strategy respects `untrusted`, so `Box untrusted` is not vacuous. -/
theorem untrusted_respected : ∃ h, Respects untrusted h :=
  untrusted_satisfiable.exists_respects

/-- Some strategy respects `noUCA`, so `Box noUCA` and the `Respects noUCA`
    hypothesis of `operator_irrelevant` are not vacuous. -/
theorem noUCA_respected : ∃ h, Respects noUCA h :=
  noUCA_satisfiable.exists_respects

theorem interlock_step (s : State) (c : Cmd) (hs : safe s) :
    safe (apply (interlock s c) s) := by
  cases s with
  | mk w k => cases w <;> cases k <;> cases c <;> simp_all [safe, hazard, apply, interlock, isUCA]

/-- A loop preserves safety when each filtered step does, for every answer
    that Γ permits. -/
theorem loop_deriv {Γ : Assumptions} {f : State → Cmd → Cmd}
    (step : ∀ s c, safe s → Γ .computer s c → safe (apply (f s c) s)) :
    ∀ n s, safe s → Deriv Γ [.computer] safe (loop f n s)
  | 0,     _, hs => .ret hs
  | n + 1, s, hs => .ask (by simp) (fun c hc => loop_deriv step n _ (step s c hs hc))

/-- Γ = untrusted ⊢ guarded n s : safe ! {computer} -/
theorem guarded_deriv : ∀ n s, safe s → Deriv untrusted [.computer] safe (guardedLoop n s) :=
  loop_deriv fun s c hs _ => interlock_step s c hs

/-- From a safe initial state, the trusted interlock preserves safety for every
    modeled computer strategy and any finite number of steps. -/
theorem guarded_robust (n : Nat) (s : State) (hs : safe s) :
    Box untrusted safe (guardedLoop n s) :=
  sound (guarded_deriv n s hs)

/-- A raw command preserves safety when it satisfies the `noUCA` restrictions. -/
theorem raw_step (s : State) (c : Cmd) (hs : safe s) (hc : noUCA .computer s c) :
    safe (apply c s) := by
  have hc : isUCA s c = false := hc
  simpa [interlock, hc] using interlock_step s c hs

/-- The raw loop preserves safety under the behavioral assumptions Γ = noUCA. -/
theorem raw_deriv : ∀ n s, safe s → Deriv noUCA [.computer] safe (rawLoop n s) :=
  loop_deriv raw_step

/-- Removing the behavioral restrictions makes the raw loop unsafe: the
    hand-written witness always requests `openCatalyst`. This is a concrete
    counterexample, not an assumption in Γ or an analysis of why the controller
    issues that command. -/
theorem raw_not_robust : ¬ Box untrusted safe (rawLoop 1 ⟨false, false⟩) := by
  intro hBox
  have := hBox (fun _ _ => .openCatalyst) (fun _ _ _ => trivial) (fun _ => [])
  simp [run, rawLoop, loop, apply, safe, hazard] at this

/-- The computer influences the guarded loop: two strategies reach different
    final states, although both are safe by `guarded_robust`. The effect row
    bounds who can influence the result; the modality bounds what the result
    can be. -/
theorem guarded_influenced :
    run (fun _ _ => .openWater) (fun _ => []) (guardedLoop 1 ⟨false, false⟩) ≠
      run (fun _ _ => .skip) (fun _ => []) (guardedLoop 1 ⟨false, false⟩) := by
  simp [run, guardedLoop, loop, interlock, isUCA, apply]

/-- One step protocol with escalation: a request for one of the two modeled
    UCAs goes to the operator instead of the valves. The operator then gives
    the command for the valves. -/
def escalate (s : State) : Protocol :=
  .ask .computer s fun c =>
    if isUCA s c then
      .ask .operator s fun d => .ret (apply d s)
    else .ret (apply c s)

/-- Γ = noUCA ⊢ escalate s : φ ! {computer}, for every φ that holds after each
    command that noUCA permits. The protocol can ask the operator, but only
    after a command that noUCA excludes. -/
theorem escalate_deriv_of {φ : State → Prop} (s : State)
    (hφ : ∀ c, noUCA .computer s c → φ (apply c s)) :
    Deriv noUCA [.computer] φ (escalate s) :=
  .ask (by simp) fun c hc => by
    have hc' : isUCA s c = false := hc
    simp only [hc', Bool.false_eq_true, if_false]
    exact .ret (hφ c hc)

/-- Γ = noUCA ⊢ escalate s : safe ! {computer}, from a safe state. -/
theorem escalate_deriv (s : State) (hs : safe s) :
    Deriv noUCA [.computer] safe (escalate s) :=
  escalate_deriv_of s (raw_step s · hs)

/-- Γ = noUCA ⊢ escalate s ! {computer}, from every state. -/
theorem escalate_effects (s : State) : Effects noUCA [.computer] (escalate s) :=
  escalate_deriv_of s fun _ _ => trivial

/-- Under noUCA, the operator cannot change the result of `escalate`, even
    though the protocol can ask it. The replacement operator strategy in `h`
    need not respect Γ. No safety assumption on `s` is needed: this uses only
    the effect judgment. It depends on Γ, not only on the syntax:
    see `operator_matters`. -/
theorem operator_irrelevant (s : State) (h h' : Strategy)
    (hR' : Respects noUCA h') (agree : ∀ r, r ≠ .operator → h r = h' r) (hist) :
    run h hist (escalate s) = run h' hist (escalate s) :=
  irrelevant_of_not_mem (escalate_effects s) .operator (by simp) h h' hR' agree hist

/-- From the state with the two valves closed, two strategies that differ only
    in the answer of the operator give two different final states of
    `escalate`. -/
theorem operator_matters :
    run (fun _ _ => .openCatalyst) (fun _ => []) (escalate ⟨false, false⟩) ≠
      run (fun r _ => if r = .operator then .closeCatalyst else .openCatalyst)
        (fun _ => []) (escalate ⟨false, false⟩) := by
  simp [run, escalate, isUCA, apply]

/-- Γ = operatorNoUCA ⊢ escalate s : safe ! {computer, operator}, from a safe
    state. The computer has no restriction. If the computer requests a UCA,
    the protocol asks the operator, and the operator avoids the UCAs. If the
    computer requests another command, that command is safe to apply. -/
theorem escalate_deriv_operatorNoUCA (s : State) (hs : safe s) :
    Deriv operatorNoUCA [.computer, .operator] safe (escalate s) :=
  .ask (by simp) fun c _ => by
    cases h : isUCA s c
    · simp only [Bool.false_eq_true, if_false]
      exact .ret (raw_step s c hs h)
    · simp only [if_true]
      exact .ask (by simp) fun d hd => .ret (raw_step s d hs (hd rfl))

/-- From a safe state, `escalate` is safe for every computer strategy, if the
    operator avoids the two modeled UCAs. Here the operator does the work of
    the interlock: the assumption on the computer in `escalate_deriv` moves
    to the operator. -/
theorem escalate_robust (s : State) (hs : safe s) :
    Box operatorNoUCA safe (escalate s) :=
  sound (escalate_deriv_operatorNoUCA s hs)

/-! ### Concrete proof trees

  Each example below is one proof tree, written as a Lean term, with the same
  tree drawn above it. All of them start from the state `⟨false, false⟩`:
  both valves are closed. The first three have one question on each path,
  and the last two have a tree of depth 2. A state `⟨w, k⟩` has the water
  valve `w` and the catalyst valve `k`.

  In each term, `.ask` is the root, `by simp` proves that the asked role is
  in the effect row, and the `match` has one arm for each answer `c` of the
  computer. `.ret rfl` is a leaf: `rfl` proves that the final state is safe.
  `nomatch` marks an answer that Γ forbids, so the tree needs no sub-tree
  for it.
-/

/-- The raw loop under `noUCA`. Γ forbids `openCatalyst` while the water valve
    is closed, so the tree needs no sub-tree for that answer. In the term,
    `hc` is the claim that Γ permits the answer, and `nomatch hc` shows that
    no such claim exists.

    ```
    noUCA ⊢ rawLoop 1 ⟨false, false⟩ : safe ! [computer]            by ask
    +-- computer ∈ [computer]
    +-- c = openWater      ⊢ ret ⟨true,  false⟩ : safe              by ret
    +-- c = closeWater     ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = openCatalyst   no sub-tree: noUCA forbids this answer
    +-- c = closeCatalyst  ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = skip           ⊢ ret ⟨false, false⟩ : safe              by ret
    ``` -/
example : Deriv noUCA [.computer] safe (rawLoop 1 ⟨false, false⟩) :=
  .ask (by simp) fun c hc =>
    match c, hc with
    | .openWater,     _  => .ret rfl
    | .closeWater,    _  => .ret rfl
    | .openCatalyst,  hc => nomatch hc
    | .closeCatalyst, _  => .ret rfl
    | .skip,          _  => .ret rfl

/-- The raw loop under `untrusted` has no proof tree. Γ permits
    `openCatalyst`, and that answer leads to the hazard, so one leaf fails.

    ```
    untrusted ⊢ rawLoop 1 ⟨false, false⟩ : safe ! [computer]        by ask
    +-- computer ∈ [computer]
    +-- c = openWater      ⊢ ret ⟨true,  false⟩ : safe              by ret
    +-- c = closeWater     ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = openCatalyst   ⊢ ret ⟨false, true⟩  : safe              fails: hazard
    +-- c = closeCatalyst  ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = skip           ⊢ ret ⟨false, false⟩ : safe              by ret
    ``` -/
example : ¬ Deriv untrusted [.computer] safe (rawLoop 1 ⟨false, false⟩) :=
  fun d => raw_not_robust (sound d)

/-- `escalate` under `noUCA`. From this state, `openCatalyst` is the only UCA,
    so it is the only answer that leads to a question for the operator, and Γ
    forbids it. So the tree asks only the computer, and the effect row is
    `[computer]`.

    ```
    noUCA ⊢ escalate ⟨false, false⟩ : safe ! [computer]             by ask
    +-- computer ∈ [computer]
    +-- c = openWater      ⊢ ret ⟨true,  false⟩ : safe              by ret
    +-- c = closeWater     ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = openCatalyst   no sub-tree: noUCA forbids this answer
    |                      (the only branch with `ask operator`)
    +-- c = closeCatalyst  ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = skip           ⊢ ret ⟨false, false⟩ : safe              by ret
    ``` -/
example : Deriv noUCA [.computer] safe (escalate ⟨false, false⟩) :=
  .ask (by simp) fun c hc =>
    match c, hc with
    | .openWater,     _  => .ret rfl
    | .closeWater,    _  => .ret rfl
    | .openCatalyst,  hc => nomatch hc
    | .closeCatalyst, _  => .ret rfl
    | .skip,          _  => .ret rfl

/-- `escalate` under `operatorNoUCA`. Γ puts no restriction on the computer,
    so the tree needs a sub-tree for `openCatalyst`. That sub-tree is a
    question to the operator, so the operator is in the effect row. Γ forbids
    the answer `openCatalyst` of the operator while the water valve is closed,
    so the sub-tree has four leaves, and each of them is safe. In the term,
    `hd rfl` is the claim that Γ permits the answer of the operator.

    ```
    operatorNoUCA ⊢ escalate ⟨false, false⟩ : safe ! [computer, operator]
                                                                    by ask
    +-- computer ∈ [computer, operator]
    +-- c = openWater      ⊢ ret ⟨true,  false⟩ : safe              by ret
    +-- c = closeWater     ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = openCatalyst   ⊢ ask operator ⟨false, false⟩ ... : safe by ask
    |   +-- operator ∈ [computer, operator]
    |   +-- d = openWater      ⊢ ret ⟨true,  false⟩ : safe          by ret
    |   +-- d = closeWater     ⊢ ret ⟨false, false⟩ : safe          by ret
    |   +-- d = openCatalyst   no sub-tree: operatorNoUCA forbids this answer
    |   +-- d = closeCatalyst  ⊢ ret ⟨false, false⟩ : safe          by ret
    |   +-- d = skip           ⊢ ret ⟨false, false⟩ : safe          by ret
    +-- c = closeCatalyst  ⊢ ret ⟨false, false⟩ : safe              by ret
    +-- c = skip           ⊢ ret ⟨false, false⟩ : safe              by ret
    ``` -/
example : Deriv operatorNoUCA [.computer, .operator] safe (escalate ⟨false, false⟩) :=
  .ask (by simp) fun c _ =>
    match c with
    | .openWater     => .ret rfl
    | .closeWater    => .ret rfl
    | .openCatalyst  =>
      .ask (by simp) fun d hd =>
        match d, hd with
        | .openWater,     _  => .ret rfl
        | .closeWater,    _  => .ret rfl
        | .openCatalyst,  hd => nomatch hd rfl
        | .closeCatalyst, _  => .ret rfl
        | .skip,          _  => .ret rfl
    | .closeCatalyst => .ret rfl
    | .skip          => .ret rfl

/-- The guarded loop under `untrusted`, with two steps. The tree has depth 2:
    each first answer `c₁` leads to a sub-tree for one more step. After
    `openWater` the state is `⟨true, false⟩`. After each of the other four
    answers the state is still `⟨false, false⟩`, so those four share one
    sub-tree.

    ```
    untrusted ⊢ guardedLoop 2 ⟨false, false⟩ : safe ! [computer]    by ask
    +-- computer ∈ [computer]
    +-- c₁ = openWater      ⊢ guardedLoop 1 ⟨true, false⟩ : safe    by ask
    |   +-- computer ∈ [computer]
    |   +-- c₂ = openWater      ⊢ ret ⟨true,  false⟩ : safe         by ret
    |   +-- c₂ = closeWater     ⊢ ret ⟨false, false⟩ : safe         by ret
    |   +-- c₂ = openCatalyst   ⊢ ret ⟨true,  true⟩  : safe         by ret
    |   +-- c₂ = closeCatalyst  ⊢ ret ⟨true,  false⟩ : safe         by ret
    |   +-- c₂ = skip           ⊢ ret ⟨true,  false⟩ : safe         by ret
    +-- c₁ = closeWater, openCatalyst, closeCatalyst or skip
        ⊢ guardedLoop 1 ⟨false, false⟩ : safe                       by ask
        +-- computer ∈ [computer]
        +-- c₂ = openWater      ⊢ ret ⟨true,  false⟩ : safe         by ret
        +-- c₂ = closeWater     ⊢ ret ⟨false, false⟩ : safe         by ret
        +-- c₂ = openCatalyst   ⊢ ret ⟨false, false⟩ : safe         by ret
        +-- c₂ = closeCatalyst  ⊢ ret ⟨false, false⟩ : safe         by ret
        +-- c₂ = skip           ⊢ ret ⟨false, false⟩ : safe         by ret
    ``` -/
example : Deriv untrusted [.computer] safe (guardedLoop 2 ⟨false, false⟩) :=
  .ask (by simp) fun c₁ _ =>
    match c₁ with
    | .openWater =>
      .ask (by simp) fun c₂ _ =>
        match c₂ with
        | .openWater     => .ret rfl
        | .closeWater    => .ret rfl
        | .openCatalyst  => .ret rfl
        | .closeCatalyst => .ret rfl
        | .skip          => .ret rfl
    | .closeWater | .openCatalyst | .closeCatalyst | .skip =>
      .ask (by simp) fun c₂ _ =>
        match c₂ with
        | .openWater     => .ret rfl
        | .closeWater    => .ret rfl
        | .openCatalyst  => .ret rfl
        | .closeCatalyst => .ret rfl
        | .skip          => .ret rfl

/-! ## 6. Limits of this demo

  This file is a minimal demo. It does not model these items:

  1. Choreographies and EPP (Endpoint Projection).
     There is only one global protocol. A real version starts from a
     choreography and uses EPP to get `Obs A` and `Action A` for each role.
     The strategy space 𝒢_A = (Obs A)* → Action A then comes from EPP.
     Here, `Obs` is the full state `State` for every role, and `Action` is
     the same type `Cmd` for every role.

  2. Effect algebra.
     There is no sequencing (`bind`) and no subeffecting rule
     (E ⊆ E' ⟹ Γ ⊢ P : φ ! E'). The effect row is a list, not a set.

  3. Liveness and fairness.
     φ is a property of the final state only. Safety at every step follows
     only because `loop n` is proved for all n. There is no temporal logic
     (□ / ◇ over traces) and no fairness hypothesis, so "monitor coverage"
     (every action is eventually inspected) cannot be stated.

  4. Additional communication and probabilistic strategies.
     A `Strategy` gives each role a function of its own history, but `Box`
     quantifies over all permitted combinations, including coordinated
     policies. Protocols can relay signals through subsequent observations.
     The model omits access to other roles' histories or shared mutable state
     beyond those observations, additional communication channels, and
     probabilistic semantics for randomized strategies. Code-based collusion
     as in Ctrl-Z would need richer observation and action types; separate
     strategy functions do not by themselves exclude that coordination.

  5. Adversary model Γ.
     Γ restricts each answer using only the current observation. It cannot
     state limits on the history (for example "at most k bad commands"),
     on time, or on the number of compromised roles ("at most f of n").
     Γ is not printed as a list of named hypotheses in a certificate.
     Types and protocol structure bound the available observations, commands
     and interactions; Γ only restricts answers within those bounds. Additional
     channels or ways to bypass the loop would require extending the model.

  6. Time.
     There is no clock. The STPA UCA (Unsafe Control Action) types
     "too early / too late" and "stopped too soon / applied too long"
     cannot be expressed. Only "provided" and "not provided" (`skip`) can.

  7. Values.
     Commands carry no data, so "wrong value" UCAs are not modeled.

  8. Decision procedure.
     Derivations are built by hand. There is no automatic proof search,
     no complexity bound, and no export to TLA+ (Temporal Logic of Actions)
     or Tamarin for differential testing.

  9. Trusted enforcement and physical behavior.
     The interlock reads the actual valve state, every requested command
     passes through it, and valves change atomically according to `apply`.
     Strategies cannot bypass or modify the interlock. Sensor errors, actuator
     failures and independent changes in the physical process are outside
     this model. Safety is proved from a safe initial state; recovery from
     an existing hazard and useful progress are not established.
-/

end Misc.SequentCalculusEffects
