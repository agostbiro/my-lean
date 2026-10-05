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

    2. Effect row → bound on influence (`frame`).
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
    Conversely, a role can be asked by the program yet have no influence,
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

    Capabilities are bounded jointly by the types and the program: `St`
    describes observations, `Cmd` describes actions, and `Prog` fixes which
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
    P  = program (a tree of `ask` effects)
    φ  = property of the final state
    E  = effect row: an upper bound on roles P may ask under Γ

  Example: a simplified chemical reactor based on the MIT STPA slides.
  Hazard H = "catalyst valve open while water valve closed".
  Source: N. Leveson, MIT 16.63J System Safety (Spring 2016), Session 10,
    "Systems Theoretic Process Analysis (STPA) Intro, Basic Components",
    slides 33–34 (causal analysis) and 36–56 (reactor). MIT OpenCourseWare:
    https://ocw.mit.edu/courses/16-63j-system-safety-spring-2016/resources/mit16_63js16_lecnotes10/

  See section 6 for the limits of this demo.
-/

namespace Misc.SequentCalculusEffects

/-! ## 1. Syntax: programs with one effect, `ask` -/

/-- The roles (controllers) in the control structure. -/
inductive Role | computer | operator
  deriving DecidableEq, Repr

/-- The state of the reactor: the positions of the two valves. -/
structure St where
  /-- The water valve is open. -/
  water    : Bool
  /-- The catalyst valve is open. -/
  catalyst : Bool
  deriving DecidableEq, Repr

/-- The commands that a role can send to the valves. -/
inductive Cmd | openWater | closeWater | openCatalyst | closeCatalyst | skip
  deriving DecidableEq, Repr

/-- A program asks roles for commands. The continuation `k` receives the answer.
    The program does not say what the answer is: a handler supplies it. -/
inductive Prog where
  | ret : St → Prog
  | ask : Role → St → (Cmd → Prog) → Prog

/-! ## 2. Semantics: handlers are strategies `Obs* → Action` -/

/-- A deterministic, total strategy for every role, using its own observation
    history. Each function describes a possible behavior of that role. -/
def Strategy := Role → List St → Cmd

/-- Run a program with a handler. `hist r` = what role `r` has observed so far. -/
def run (h : Strategy) (hist : Role → List St) : Prog → St
  | .ret s => s
  | .ask A o k =>
    let hist' := fun r => if r = A then o :: hist r else hist r
    run h hist' (k (h A (hist' A)))

/-- Behavioral assumptions Γ: `Γ A o c` = "role A may answer c when it observes o".
    Allowing every command models an untrusted role; allowing exactly one per
    observation fixes a policy based only on the current observation. Γ adds
    restrictions within the capabilities provided by the types and program.
    `Box` below quantifies over every strategy that respects these restrictions.
    Γ should be `Serial`: otherwise no strategy respects it. -/
def Model := Role → St → Cmd → Prop

/-- Γ permits at least one command for every role and observation. -/
def Serial (Γ : Model) : Prop := ∀ A o, ∃ c, Γ A o c

/-- The strategy `h` stays inside Γ: every answer of every role is one that
    Γ permits for the current observation. This covers all roles, histories
    and observations, including ones that no run reaches. -/
def Respects (Γ : Model) (h : Strategy) : Prop :=
  ∀ A hs o, Γ A o (h A (o :: hs))

/-- A serial Γ is respected by some strategy, so `Box Γ` is not vacuous. -/
theorem Serial.exists_respects {Γ : Model} (hΓ : Serial Γ) : ∃ h, Respects Γ h :=
  ⟨fun A hs => match hs with
    | []     => .skip
    | o :: _ => Classical.choose (hΓ A o),
   fun A _ o => Classical.choose_spec (hΓ A o)⟩

/-- The robustness modality □_Γ φ: the final state satisfies φ for every
    strategy that Γ permits and every initial history. If Γ is not `Serial`,
    no strategy respects it and `Box Γ φ P` holds for every φ and P. -/
def Box (Γ : Model) (φ : St → Prop) (P : Prog) : Prop :=
  ∀ h, Respects Γ h → ∀ hist, φ (run h hist P)

/-! ## 3. The sequent calculus: two rules -/

/-- `Deriv Γ E φ P`  ≈  Γ ⊢ P : φ ! E -/
inductive Deriv (Γ : Model) (E : List Role) (φ : St → Prop) : Prog → Prop
  /-- ret:  φ s  ⟹  Γ ⊢ ret s : φ ! E -/
  | ret {s} : φ s → Deriv Γ E φ (.ret s)
  /-- ask (left rule for the effect): A ∈ E, and for every answer c that Γ permits,
      Γ ⊢ k c : φ ! E  ⟹  Γ ⊢ ask A o k : φ ! E -/
  | ask {A o k} : A ∈ E → (∀ c, Γ A o c → Deriv Γ E φ (k c)) →
      Deriv Γ E φ (.ask A o k)

/-- `Effects Γ E P`  ≈  Γ ⊢ P ! E: the effect row alone, with no claim about
    the final state. -/
abbrev Effects (Γ : Model) (E : List Role) : Prog → Prop := Deriv Γ E (fun _ => True)

/-! ## 4. Metatheory -/

/-- Every derivation gives the effect judgment: drop the final property. -/
theorem Deriv.effects {Γ E φ P} (d : Deriv Γ E φ P) : Effects Γ E P := by
  induction d with
  | ret _ => exact .ret trivial
  | ask hA _ ih => exact .ask hA ih

/-- Soundness: a derivation establishes the final property for all permitted
    handlers, giving the robustness modality. -/
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

/-- Effect rows bound influence: with initial histories fixed, changing only a
    role outside E from a strategy profile `h'` that respects Γ leaves the
    result unchanged. No restriction on that role's replacement is needed.
    Only the effect judgment is used: apply `Deriv.effects` to a derivation. -/
theorem frame {Γ E P} (d : Effects Γ E P) (B : Role) (hB : B ∉ E)
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
def hazard (s : St) : Bool := s.catalyst && !s.water

/-- A state is safe if it is not in the hazard. -/
def safe (s : St) : Prop := hazard s = false

/-- The effect of a command on the state. -/
def apply : Cmd → St → St
  | .openWater,     s => { s with water := true }
  | .closeWater,    s => { s with water := false }
  | .openCatalyst,  s => { s with catalyst := true }
  | .closeCatalyst, s => { s with catalyst := false }
  | .skip,          s => s

/-- The two modeled UCAs (Unsafe Control Actions): opening the catalyst valve
    while the water valve is closed, and closing the water valve while the
    catalyst valve is open. -/
def isUCA (s : St) : Cmd → Bool
  | .openCatalyst => !s.water
  | .closeWater   => s.catalyst
  | _             => false

/-- Trusted interlock: uses the actual valve state to block the two modeled UCAs. -/
def interlock (s : St) (c : Cmd) : Cmd := if isUCA s c then .skip else c

/-- n control steps. Each step asks the computer, then filters the command. -/
def loop (filter : St → Cmd → Cmd) : Nat → St → Prog
  | 0,     s => .ret s
  | n + 1, s => .ask .computer s (fun c => loop filter n (apply (filter s c) s))

/-- The control loop with no interlock: every command goes to the valves. -/
def raw     := loop (fun _ c => c)

/-- The control loop with the interlock. -/
def guarded := loop interlock

/-- No behavioral restrictions on any role. Every strategy in the chosen
    language respects this model. The reactor loop asks only the computer. -/
def untrusted : Model := fun _ _ _ => True

/-- Behavioral assumption: every role avoids the two modeled UCAs.
    This encodes constraints used by the example, not the STPA methodology. -/
def noUCA : Model := fun _ s c => isUCA s c = false

/-! ### Proofs -/

theorem untrusted_serial : Serial untrusted := fun _ _ => ⟨.skip, trivial⟩

theorem noUCA_serial : Serial noUCA := fun _ _ => ⟨.skip, rfl⟩

/-- Some strategy respects `untrusted`, so `Box untrusted` is not vacuous. -/
theorem untrusted_respected : ∃ h, Respects untrusted h :=
  untrusted_serial.exists_respects

/-- Some strategy respects `noUCA`, so `Box noUCA` and the `Respects noUCA`
    hypothesis of `operator_irrelevant` are not vacuous. -/
theorem noUCA_respected : ∃ h, Respects noUCA h :=
  noUCA_serial.exists_respects

theorem interlock_step (s : St) (c : Cmd) (hs : safe s) :
    safe (apply (interlock s c) s) := by
  cases s with
  | mk w k => cases w <;> cases k <;> cases c <;> simp_all [safe, hazard, apply, interlock, isUCA]

/-- A loop preserves safety when each filtered step does, for every answer
    that Γ permits. -/
theorem loop_deriv {Γ : Model} {f : St → Cmd → Cmd}
    (step : ∀ s c, safe s → Γ .computer s c → safe (apply (f s c) s)) :
    ∀ n s, safe s → Deriv Γ [.computer] safe (loop f n s)
  | 0,     _, hs => .ret hs
  | n + 1, s, hs => .ask (by simp) (fun c hc => loop_deriv step n _ (step s c hs hc))

/-- Γ = untrusted ⊢ guarded n s : safe ! {computer} -/
theorem guarded_deriv : ∀ n s, safe s → Deriv untrusted [.computer] safe (guarded n s) :=
  loop_deriv fun s c hs _ => interlock_step s c hs

/-- From a safe initial state, the trusted interlock preserves safety for every
    modeled computer strategy and any finite number of steps. -/
theorem guarded_robust (n : Nat) (s : St) (hs : safe s) :
    Box untrusted safe (guarded n s) :=
  sound (guarded_deriv n s hs)

/-- A raw command preserves safety when it satisfies the `noUCA` restrictions. -/
theorem raw_step (s : St) (c : Cmd) (hs : safe s) (hc : noUCA .computer s c) :
    safe (apply c s) := by
  have hc : isUCA s c = false := hc
  simpa [interlock, hc] using interlock_step s c hs

/-- The raw loop preserves safety under the behavioral assumptions Γ = noUCA. -/
theorem raw_deriv : ∀ n s, safe s → Deriv noUCA [.computer] safe (raw n s) :=
  loop_deriv raw_step

/-- Removing the behavioral restrictions makes the raw loop unsafe: the
    hand-written witness always requests `openCatalyst`. This is a concrete
    counterexample, not an assumption in Γ or an analysis of why the controller
    issues that command. -/
theorem raw_not_robust : ¬ Box untrusted safe (raw 1 ⟨false, false⟩) := by
  intro hBox
  have := hBox (fun _ _ => .openCatalyst) (fun _ _ _ => trivial) (fun _ => [])
  simp [run, raw, loop, apply, safe, hazard] at this

/-- The computer influences the guarded loop: two strategies reach different
    final states, although both are safe by `guarded_robust`. The effect row
    bounds who can influence the result; the modality bounds what the result
    can be. -/
theorem guarded_influenced :
    run (fun _ _ => .openWater) (fun _ => []) (guarded 1 ⟨false, false⟩) ≠
      run (fun _ _ => .skip) (fun _ => []) (guarded 1 ⟨false, false⟩) := by
  simp [run, guarded, loop, interlock, isUCA, apply]

/-- One step with escalation: a request to open the catalyst valve while the
    water valve is closed goes to the operator instead of the valves. -/
def escalate (s : St) : Prog :=
  .ask .computer s fun c =>
    if c = .openCatalyst ∧ s.water = false then
      .ask .operator s fun d => .ret (apply d s)
    else .ret (apply c s)

/-- Γ = noUCA ⊢ escalate s : φ ! {computer}, for every φ that holds after each
    command that noUCA permits. The program can ask the operator, but only
    after a command that noUCA excludes. -/
theorem escalate_deriv_of {φ : St → Prop} (s : St)
    (hφ : ∀ c, noUCA .computer s c → φ (apply c s)) :
    Deriv noUCA [.computer] φ (escalate s) :=
  .ask (by simp) fun c hc => by
    have hc' : ¬ (c = .openCatalyst ∧ s.water = false) := by
      rintro ⟨rfl, hw⟩
      simp [noUCA, isUCA, hw] at hc
    simp only [if_neg hc']
    exact .ret (hφ c hc)

/-- Γ = noUCA ⊢ escalate s : safe ! {computer}, from a safe state. -/
theorem escalate_deriv (s : St) (hs : safe s) :
    Deriv noUCA [.computer] safe (escalate s) :=
  escalate_deriv_of s (raw_step s · hs)

/-- Γ = noUCA ⊢ escalate s ! {computer}, from every state. -/
theorem escalate_effects (s : St) : Effects noUCA [.computer] (escalate s) :=
  escalate_deriv_of s fun _ _ => trivial

/-- Under noUCA, the operator cannot change the result of `escalate`, even
    though the program can ask it. The replacement operator strategy in `h`
    need not respect Γ. No safety assumption on `s` is needed: this uses only
    the effect judgment. It depends on Γ, not only on the syntax:
    see `operator_matters`. -/
theorem operator_irrelevant (s : St) (h h' : Strategy)
    (hR' : Respects noUCA h') (agree : ∀ r, r ≠ .operator → h r = h' r) (hist) :
    run h hist (escalate s) = run h' hist (escalate s) :=
  frame (escalate_effects s) .operator (by simp) h h' hR' agree hist

/-- Without the noUCA restriction on the computer, the operator does change
    the result of `escalate`. -/
theorem operator_matters :
    run (fun _ _ => .openCatalyst) (fun _ => []) (escalate ⟨false, false⟩) ≠
      run (fun r _ => if r = .operator then .closeCatalyst else .openCatalyst)
        (fun _ => []) (escalate ⟨false, false⟩) := by
  simp [run, escalate, apply]

/-! ## 6. Limits of this demo

  This file is a minimal demo. It does not model these items:

  1. Choreographies and EPP (Endpoint Projection).
     There is only one global program. A real version starts from a
     choreography and uses EPP to get `Obs A` and `Action A` for each role.
     The strategy space 𝒢_A = (Obs A)* → Action A then comes from EPP.
     Here, `Obs` is the full state `St` for every role, and `Action` is
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
     policies. Programs can relay signals through subsequent observations.
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
     Types and program structure bound the available observations, commands
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
