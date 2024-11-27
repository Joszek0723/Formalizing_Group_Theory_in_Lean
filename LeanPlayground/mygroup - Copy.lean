import Mathlib.Tactic

/- An effort to build groups from scratch-/

/- There was a lot of flailing around to get it to accept normal way of writing multiplication, inverses and identity elements, and
I did not get it to work with the identity element.
-/

set_option quotPrecheck false

variable {myGroup: Type U}
variable {I: myGroup }
variable {mul:myGroup→ myGroup→ myGroup}
variable {inv:myGroup → myGroup}

axiom axassoc1: ∀ (g h k:myGroup),(mul g (mul h k)) = (mul (mul g h) k)
axiom axassoc2: ∀ (g h k:myGroup),(mul (mul g h) k) = (mul g (mul h k))
axiom axinv : ∀ (g: myGroup), (mul g (inv g)) = I ∧ (mul (inv g) g) = I
axiom axid :∀ (g: myGroup), mul g I=g  ∧ mul I g = g

#check axinv
postfix:max  "⁻¹" =>  inv
infixl:100  " * "  => mul
/-notation " I " => one   not sure how to make it be 1-/

/- Just to see how the notational stuff is working -/
example  {b:myGroup}:mul b (inv b) = I :=   by apply And.left (axinv b)
example {b: myGroup} : mul b (b⁻¹) = I := by apply And.left (axinv b)
example {b: myGroup} : b * b⁻¹ = I := by apply And.left (axinv b)
example {b: myGroup} : b * b⁻¹ = I := by apply And.left (axinv b)


example {a b c:myGroup}:   (mul a (mul b c))=(mul (mul a b) c)   :=  by apply axassoc1 a b c

/- Now a real theorem.  The identity is unique; there's
both a left and right version.  The first says there's a unique
left identity. -/

theorem unique_id_left (z: myGroup)(h : ∀ (g:myGroup),z*g = g):z = I := by
have h₁: z*I = z  :=  (And.left (axid z))
have h₁₁: z = z* I := Eq.symm h₁
have h₂: z * I = I := h I
exact Eq.trans h₁₁ h₂

/-Can't we do this with a calculational proof? We can! -/

theorem unique_id_left2 (z: myGroup)(h : ∀ (g:myGroup),z*g = g):z = I := by
calc
z = z * I := Eq.symm (And.left (axid z))
_ = I := h I

/-! Problems from the chapter on groups in Herstein's  _Topics in Algebra_,
both the theorems in the chapter text and exercises.-/

/- unique right identity -/
theorem unique_id_right (z: myGroup)(h : ∀ (g:myGroup),g * z = g):z = I := by
calc
z = I * z := Eq.symm (And.right (axid z))
_   = I := h I

/-unique left inverse -/

theorem unique_left_inverse (a b :myGroup)(h: b * a = I): b = a⁻¹ := by
have ha: I = a * a⁻¹  := Eq.symm (And.left (axinv a))
calc
b = b * I := Eq.symm (And.left (axid b))
_ = b * (a * a⁻¹):= by rw [ha]
_ = (b * a) * a⁻¹ :=  (axassoc1 b a a⁻¹)
_ = I * a⁻¹ := by rw [h]
_ = a⁻¹ := And.right (axid a⁻¹)

theorem inverse_inverse {mul:myGroup→ myGroup→ myGroup}{inv:myGroup → myGroup}(a I: myGroup) : inv (inv a) = a := by
  have h₁: mul a (inv a) = I  := And.left (axinv a)
  have h₂: a = inv (inv a) := (unique_left_inverse (inv a) a h₁)
  exact Eq.symm (h₂)

theorem inv_mul (I: myGroup)(a b : myGroup) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h₁ : (b⁻¹ * a⁻¹) * (a * b) = I := by
    have h₂ : (b⁻¹ * a⁻¹) * (a * b) = b⁻¹ * (a⁻¹ * (a * b)) := axassoc2 b⁻¹ a⁻¹ (a * b)
    have h₃ : a⁻¹ * (a * b) = (a⁻¹ * a) * b := axassoc1 a⁻¹ a b
    rw [h₃] at h₂
    have h₄ : a⁻¹ * a = I := And.right (axinv a)
    rw [h₄] at h₂
    have h₅ : I * b = b := And.right (axid b)
    rw [h₅] at h₂
    have h₆ : b⁻¹ * b = I := And.right (axinv b)
    rw [h₆] at h₂
    exact h₂
  exact Eq.symm (unique_left_inverse (a * b) (b⁻¹ * a⁻¹) h₁)

theorem left_cancellation (inv:myGroup → myGroup)(a u w I: myGroup) : mul a u = mul a w → u = w := by
  intro h
  have h₁: inv a * (a * u) = inv a * (a * w) := by
    rw[h]
  have h₂: inv a * (a * u) = (inv a * a) * u := axassoc1 (inv a) a u
  rw [h₂] at h₁
  have h₃: inv a * (a * w) = (inv a * a) * w := axassoc1 (inv a) a w
  rw [h₃] at h₁
  have h₄: inv a * a = I := And.right (axinv a)
  rw [h₄] at h₁
  have h₅: I * u = u := And.right (axid u)
  rw [h₅] at h₁
  have h₆: I * w = w := And.right (axid w)
  rw [h₆] at h₁
  exact h₁

theorem right_cancellation (inv:myGroup → myGroup)(a u w I: myGroup): mul u a = mul w a → u = w := by
  intro h
  have h₁: (u * a) * inv a = (w * a) * inv a := by
    rw[h]
  have h₂: (u * a) * inv a = u * (a * inv a) := axassoc2 u a (inv a)
  rw [h₂] at h₁
  have h₃: (w * a) * inv a = w * (a * inv a) := axassoc2 w a (inv a)
  rw [h₃] at h₁
  have h₄: a * inv a = I := And.left (axinv a)
  rw [h₄] at h₁
  have h₅: u * I = u := And.left (axid u)
  rw [h₅] at h₁
  have h₆: w * I = w := And.left (axid w)
  rw [h₆] at h₁
  exact h₁

def pow (mul : myGroup → myGroup → myGroup) (I : myGroup) (a : myGroup) (n : ℕ) : myGroup :=
  match n with
  | 0        => I
  | n + 1    => mul a (pow mul I a n)

notation a " ^ " n => pow mul I a n

theorem questionTwo (n : ℕ) (a b : myGroup)  (h : ∀ x y : myGroup, mul x y = mul y x) :
  pow mul I (mul a b) n = mul (pow mul I a n) (pow mul I b n) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    calc
      pow mul I (mul a b) 0 = I := rfl
      _ = mul I I := Eq.symm (And.left (axid I))
      _ = mul (pow mul I a 0) (pow mul I b 0) := rfl
  | succ n ih =>
    -- Inductive step: Assume the statement holds for n, prove for n + 1
    have h₁ : pow mul I (mul a b) (n + 1) = mul (mul a b) (pow mul I (mul a b) n) := rfl
    have h₂ : pow mul I (mul a b) n =  (mul (pow mul I a n) (pow mul I b n)) := ih
    rw [h₂] at h₁
    have h₃ : mul (mul a b) (mul (pow mul I a n) (pow mul I b n)) = mul (mul (mul a b) (pow mul I a n)) (pow mul I b n) := axassoc1 (mul a b) (pow mul I a n) (pow mul I b n)
    rw [h₃] at h₁
    have h₄ : mul (mul a b) (pow mul I a n) = mul a (mul b (pow mul I a n)) := axassoc2 a b (pow mul I a n)
    rw [h₄] at h₁
    have h₅ : mul b (pow mul I a n) = mul (pow mul I a n) b := h b (pow mul I a n)
    rw [h₅] at h₁
    have h₆ : mul a (mul (pow mul I a n) b) = mul (mul a (pow mul I a n)) b := axassoc1 a (pow mul I a n) b
    rw [h₆] at h₁
    have h₇ : mul a (pow mul I a n) = pow mul I a (n+1) := rfl
    rw [h₇] at h₁
    have h₈ : mul (mul (pow mul I a (n + 1)) b) (pow mul I b n) = mul (pow mul I a (n + 1)) (mul b (pow mul I b n)) := axassoc2 (pow mul I a (n + 1)) b (pow mul I b n)
    rw [h₈] at h₁
    have h₉ : mul b (pow mul I b n) = pow mul I b (n + 1) := rfl
    rw[h₉] at h₁
    exact h₁


theorem questionThree {inv:myGroup → myGroup}(a b I : myGroup) (h : (a * a) * (b * b) = (a * b) * (a * b)) : a * b = b * a := by
  have h₁ : (a * b) * (a * b) = (a * a) * (b * b) := Eq.symm h
  have h₂ : (a * b) * (a * b) = a * (b * (a * b)) := axassoc2 a b (a * b)
  rw [h₂] at h₁
  have h₃ : (a * a) * (b * b) = a * (a * (b * b)) := axassoc2 a a (b * b)
  rw [h₃] at h₁
  have h₄ : b * (a * b) = a * (b * b) :=  (left_cancellation inv a (b * (a * b)) (a * (b * b)) I) h₁
  have h₅ : b * (a * b) = (b * a) * b := axassoc1 b a b
  rw [h₅] at h₄
  have h₆ : a * (b * b) = (a * b) * b := axassoc1 a b b
  rw [h₆] at h₄
  have h₇ : (b * a) = (a * b) := (right_cancellation inv b (b * a) (a * b) I) h₄
  exact Eq.symm h₇


/- Declare H as a subset of myGroup -/
variable {H : myGroup → Prop}  -- H x means x ∈ H

/- Axioms stating that H is a subgroup -/
axiom H_contains_I : H I                                       -- H contains the identity element
axiom H_closed_mul : ∀ x y, H x → H y → H (mul x y)              -- H is closed under multiplication
axiom H_closed_inv : ∀ x, H x → H (x⁻¹)                        -- H is closed under taking inverses

/- Axioms defining the left coset gH -/
variable {left_coset : myGroup → myGroup → Prop}  -- left_coset g x means x ∈ gH

/- Axiom stating the definition of the left coset -/
axiom left_coset_def : ∀ g x, left_coset g x ↔ ∃ h, H h ∧ x = h * g

theorem subgroup_coset_bijection (g : myGroup) :
  ∃ f : myGroup → myGroup,
    (∀ x : myGroup, H x → left_coset g (f x)) ∧             -- f maps H into the coset C
    (∀ x1 x2 : myGroup, H x1 → H x2 → f x1 = f x2 → x1 = x2) ∧  -- f is injective on H
    (∀ y : myGroup, left_coset g y → ∃ x : myGroup, H x ∧ f x = y)  -- f is surjective onto C
:= by
  sorry


-- theorem left_coset_inclusion
--   (h₁ h₂ : myGroup) (H_h₁ : H h₁) (H_h₂ : H h₂)
--   (x : myGroup) (h₁g₁_eq_x : mul h₁ g₁ = x) (h₂g₂_eq_x : mul h₂ g₂ = x) :
--   ∀ y, left_coset g₁ y → left_coset g₂ y := by
--   intros y h
--   -- Use the definition of left_coset for g₁ to extract h₁'
--   obtain ⟨h₁', H_h₁', y_eq_g₁h₁'⟩ := (left_coset_def g₁ y).mp h
--   -- Rewrite g₁ in terms of h₁ and x
--   have g₁_eq : g₁ = mul (h₁⁻¹) x := by
--     rw [← h₁g₁_eq_x]
--     simp [mul_assoc, mul_left_inv, mul_one]
--   rw [g₁_eq] at y_eq_g₁h₁'
--   -- Now y = (h₁⁻¹ * x) * h₁'
--   let h₂' := mul (mul (mul h₁⁻¹ x) h₁') g₂⁻¹
--   -- Verify that h₂' ∈ H
--   have H_h₂' : H h₂' := by
--     rw [← h₂g₂_eq_x, mul_assoc, mul_inv_cancel_right, ← mul_assoc]
--     apply H_closed_mul
--     · apply H_closed_mul
--       · apply H_closed_inv; exact H_h₁
--       · exact H_h₂
--     · exact H_h₁'
--   -- Show that y ∈ g₂H using h₂'
--   rw [← h₂g₂_eq_x, mul_assoc] at y_eq_g₁h₁'
--   rw [← h₁g₁_eq_x] at y_eq_g₁h₁'
--   exact (left_coset_def g₂ y).mpr ⟨h₂', H_h₂', y_eq_g₁h₁'⟩


theorem left_coset_inclusion
  {inv:myGroup → myGroup}(h₁ h₂ : myGroup) (H_h₁ : H h₁) (H_h₂ : H h₂)
  (x I : myGroup) (h₁g₁_eq_x : mul h₁ g₁ = x) (h₂g₂_eq_x : mul h₂ g₂ = x) :
  ∀ y, left_coset g₁ y → left_coset g₂ y := by
  intros y h
  have hexists : ∃ h, H h ∧ y = h * g₁ := (left_coset_def g₁ y).mp h
  cases' hexists with w h₁'
  have h₂' : y = mul w g₁ := And.right h₁'
  have h₃' : x = x := rfl
  have h₄' : mul h₁ g₁ = x := h₁g₁_eq_x
  have h₅' : mul h₂ g₂ = x := h₂g₂_eq_x
  have h₆' : mul h₁ g₁ = mul h₂ g₂ := by rw [h₅', h₄']
  have h₇' : mul (inv h₁) (mul h₁ g₁) = mul (inv h₁) (mul h₂ g₂) := by rw[h₆']
  have h₈' : mul (inv h₁) (mul h₁ g₁) = mul (mul (inv h₁) h₁) g₁ := axassoc1 (inv h₁) h₁ g₁
  rw[h₈'] at h₇'
  have h₉' : mul (inv h₁) h₁ = I := And.right (axinv h₁)
  rw [h₉'] at h₇'
  have h₁₀' : mul I g₁ = g₁ := And.right (axid g₁)
  rw [h₁₀'] at h₇'
  rw [h₇'] at h₂'
  have h₁₁' : mul (inv h₁) (mul h₂ g₂) = mul (mul (inv h₁) h₂) g₂ := axassoc1 (inv h₁) h₂ g₂
  rw [h₁₁'] at h₂'
  have h₁₂' : mul w (mul (mul (inv h₁) h₂) g₂) = mul (mul w (mul (inv h₁) h₂)) g₂ := axassoc1 w (mul (inv h₁) h₂) g₂
  rw [h₁₂'] at h₂'
  let v := mul w (mul (inv h₁) h₂)
  have Hv : H v := by
    apply H_closed_mul
    · exact H_closed_mul w (inv h₁) (And.left h₁') (And.right (axinv h₁))
    · exact H_h₂
  have : y = mul v g₂ := by
    rw [h₂']
  apply left_coset_def g₂
  use v
  constructor
  · exact Hv
  · rfl

  -- have h₇' : g₁ = inv h₁ * (h₂ * g₂) := by
  --   rw [← axassoc2 inv h₁ h₁ g₁]  -- Group h₁⁻¹ and h₁ first
  --   rw [And.left (axinv h₁)]    -- Simplify h₁⁻¹ * h₁ to I
  --   rw [And.right (axid g₁)]   -- Simplify I * g₁ to g₁


  -- ∃ h (h∈ H ∧ y=g₁ * h)
  -- exists elimination
  -- (a ∈ H ∧ y = g₁ a)
  -- And.right y=g₁ a
  -- y = g₂ a
  -- ∃ h y=g₂ h
