import Mathlib.Tactic

/- An effort to build groups from scratch-/

/- There was a lot of flailing around to get it to accept normal way of writing multiplication, inverses and identity elements, and
I did not get it to work with the identity element.
-/

set_option quotPrecheck false


variable {myGroup: Type}
variable {I: myGroup }
variable {mul:myGroup→ myGroup→ myGroup}
variable {inv:myGroup → myGroup }



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

theorem inverse_inverse (a I: myGroup) : (a⁻¹)⁻¹ = a := by
  sorry
  -- have h₁ : a⁻¹ * (a⁻¹)⁻¹ = I := And.left (axinv a⁻¹)
  -- exact unique_left_inverse a⁻¹ a h₁

theorem inv_mul (a b I : myGroup) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
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


theorem left_cancellation (a u w : myGroup) : mul a u = mul a w → u = w := by
  sorry
-- intro h -- Assume `mul a u = mul a w`
-- have h₁: (a⁻¹ * a) * u = (a⁻¹ * a) * w := by
--   rw [h] -- Multiply both sides of the equality by `a⁻¹` on the left
-- have h₂: I * u = I * w := by
--   rw [←axassoc1, ←axassoc1] at h₁ -- Apply associativity twice to regroup
--   exact h₁
-- have h₃: u = w := by
--   rw [And.right (axid u), And.right (axid w)] at h₂ -- Simplify `I * u = u` and `I * w = w`
--   exact h₂
-- exact h₃


theorem right_cancellation (a u w: myGroup): mul u a = mul w a → u = w := by
  sorry

def pow (a : myGroup) : ℕ → myGroup
| 0       => I
| (n + 1) => a * pow a n

notation a " ^ " n => pow a n

theorem questionTwo (n : ℕ) (a b : myGroup) (h : a * b = b * a) : (a * b) ^ n = a ^ n * b ^ n := by
  -- induction n with
  -- | zero =>
  --   -- Base case: n = 0
  --   rw [pow, pow, pow, pow]
  --   rw [I]
  --   rw [I * I]
  -- | succ n ih =>
  --   -- Inductive step
  --   rw [pow, pow, pow, pow]
  --   rw [←mul_assoc, h, mul_assoc a b (pow (a * b) n)]
  --   rw [ih]
  --   rw [mul_assoc, ←mul_assoc b (a ^ n) (b ^ n)]
  --   rw [h, mul_assoc]
  sorry

-- theorem question3 (a b: myGroup) (h: (a * a) * (b * b) = (a * b) * (a * b)): a * b = b * a := by
--   have h₁: (a * b) * (a * b) = (a * a) * (b * b) := Eq.symm h
--   have h₂: (a * b) * (a * b) = a * (b * (a * b)) := axassoc2 a b (a * b)
--   rw [h₂] at h₁
--   have h₃: b * (a * b) = (b * a) * b := axassoc1 b a b
--   rw [h₃] at h₁

theorem questionThree (a b : myGroup) (h : (a * a) * (b * b) = (a * b) * (a * b)) : a * b = b * a := by
  have h₁ : (a * b) * (a * b) = (a * a) * (b * b) := Eq.symm h
  have h₂ : (a * b) * (a * b) = a * (b * (a * b)) := axassoc2 a b (a * b)
  rw [h₂] at h₁
  have h₃ : (a * a) * (b * b) = a * (a * (b * b)) := axassoc2 a a (b * b)
  rw [h₃] at h₁
  have h₄ : b * (a * b) = a * (b * b) := left_cancellation a (b * (a * b)) (a * (b * b)) h₁
  have h₅ : b * (a * b) = (b * a) * b := axassoc1 b a b
  rw [h₅] at h₄
  have h₆ : a * (b * b) = (a * b) * b := axassoc1 a b b
  rw [h₆] at h₄
  have h₇ : (b * a) = (a * b) := right_cancellation b (b * a) (a * b) h₄
  exact Eq.symm h₇

/- Declare H as a subset of myGroup -/
variable {H : myGroup → Prop}  -- H x means x ∈ H

/- Axioms stating that H is a subgroup -/
axiom H_contains_I : H I                                       -- H contains the identity element
axiom H_closed_mul : ∀ x y, H x → H y → H (x * y)              -- H is closed under multiplication
axiom H_closed_inv : ∀ x, H x → H (x⁻¹)                        -- H is closed under taking inverses

/- Axioms defining the left coset gH -/
variable {left_coset : myGroup → myGroup → Prop}  -- left_coset g x means x ∈ gH

/- Axiom stating the definition of the left coset -/
axiom left_coset_def : ∀ g x, left_coset g x ↔ ∃ h, H h ∧ x = g * h

theorem subgroup_coset_bijection (g : myGroup) :
  ∃ f : myGroup → myGroup,
    (∀ x : myGroup, H x → left_coset g (f x)) ∧             -- f maps H into the coset C
    (∀ x1 x2 : myGroup, H x1 → H x2 → f x1 = f x2 → x1 = x2) ∧  -- f is injective on H
    (∀ y : myGroup, left_coset g y → ∃ x : myGroup, H x ∧ f x = y)  -- f is surjective onto C
:= by
  sorry