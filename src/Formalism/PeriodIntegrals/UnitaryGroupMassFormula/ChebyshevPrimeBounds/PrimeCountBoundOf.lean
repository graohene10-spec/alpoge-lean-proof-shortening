import Mathlib
import Formalism.PeriodIntegrals.PrimeCount

noncomputable section

namespace PI.PC

open Real

def chA : ℝ := log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30

def lf (x : ℝ) : ℝ := log ((Nat.factorial ⌊x⌋₊ : ℕ) : ℝ)

def chD (x : ℝ) : ℝ := lf x - lf (x / 2) - lf (x / 3) - lf (x / 5) + lf (x / 30)

def LfUpper : Prop := ∀ y : ℝ, 1 ≤ y → lf y ≤ y * log y - y + log y / 2 + 1

def LfLower : Prop := ∀ y : ℝ, 1 ≤ y → y * log y - y - log y / 2 + 9 / 10 ≤ lf y

def ANum : Prop := 0.92129 ≤ chA ∧ chA ≤ 0.9213

def DUpper : Prop := ∀ x : ℝ, 30 ≤ x → chD x ≤ chA * x + 5 / 2 * log x - 4

def DLower : Prop := ∀ x : ℝ, 30 ≤ x → chA * x - 5 / 2 * log x + 2 ≤ chD x

def Sandwich : Prop := ∀ x : ℝ, 0 ≤ x →
  Chebyshev.psi x - Chebyshev.psi (x / 6) ≤ chD x ∧ chD x ≤ Chebyshev.psi x

def CHUpper : Prop := ∀ x : ℝ, 1 ≤ x → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2

def CHLower : Prop := ∀ x : ℝ, 30 ≤ x → 0.92129 * x - 5 / 2 * log x ≤ Chebyshev.psi x

def PCLarge (x₀ : ℝ) : Prop := ∀ y : ℝ, x₀ ≤ y → ((pr y).card : ℝ) < 1.26 * y / log y

def PCSmall (x₀ : ℝ) : Prop := ∀ y : ℝ, 1 < y → y < x₀ → ((pr y).card : ℝ) < 1.26 * y / log y

theorem primeCountBound_of (x₀ : ℝ) (hL : PCLarge x₀) (hS : PCSmall x₀) : PI.PrimeCountBound := by
  intro y hy
  exact (le_or_gt x₀ y).elim (fun h => hL y h) (fun h => hS y hy h)

theorem chLower_of (hA : ANum) (hD : DLower) (hS : Sandwich) : CHLower := by
  intro x hx
  linarith [hD x hx, (hS x (by linarith)).2,
    mul_le_mul_of_nonneg_right hA.1 (show (0 : ℝ) ≤ x by linarith)]

end PI.PC
