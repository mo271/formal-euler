import Mathlib

/-!
# Observationes de theoremate quodam Fermatiano aliisque ad numeros primos spectantibus
Commentatio 26 indices Enestroemiani

Commentarii academiae scientiarum Petropolitanae 6 (1732/3), 1738, p. 103-107
-/

namespace Euler.SeriesPrima.Volumen2.E26

open Nat

/-!
Notum est hanc quantitatem $a^n+1$ semper habere divisores, quoties $n$ sit numerus impar
vel per imparem praeter unitatem divisibilis.
Namque $a^{2m+1}+1$ dividi potest per $a+1$...
-/
theorem divisibilitas_impar (a m : ℕ) :
    (a + 1) ∣ (a ^ (2 * m + 1) + 1) := by
  convert (Odd.nat_add_dvd_pow_add_pow a 1 ⟨m, rfl⟩)
  norm_num

/-!
...et $a^{p(2m+1)}+1$ per $a^p+1$, quicunque etiam numerus loco $a$ substituatur.
-/
theorem divisibilitas_generalis (a m p : ℕ) :
    (a ^ p + 1) ∣ (a ^ (p * (2 * m + 1)) + 1) := by
  have := Odd.nat_add_dvd_pow_add_pow (a^p) 1 ⟨m, rfl⟩
  rwa [pow_mul,one_pow] at *

/-!
Quamobrem si qui sunt numeri primi huius formae $a^n+1$, ii omnes comprehendantur necesse est
in hac forma $a^{2^m}+1$.
-/
theorem forma_numerorum_primorum (a n : ℕ) (h_prime : (a ^ n + 1).Prime) (ha : 1 < a) (hn : 1 < n) :
    ∃ m : ℕ, n = 2 ^ m := by
  -- TODO(firsching)
  by_contra hm
  simp at hm
  have : ∃ m > 0, ∃ p > 1, n = p * (2 * m + 1) := by
    by_cases h : n.primeFactors = {2}
    · absurd hm
      push_neg
      sorry
    · have : ∃ q, q ∈ n.primeFactors ∧ 2 < q := by
        sorry
      obtain ⟨q, ⟨hq1, hq2⟩ ⟩ := this
      simp at hq1
      obtain ⟨hq_prime, hq_div, hq_ne_zero⟩ := hq1
      obtain ⟨m, hm⟩ := (hq_prime).odd_of_ne_two (@hq2).ne'
      use m
      constructor
      · omega
      · use n / q
        constructor
        · sorry
        · rw [← hm]
          exact Eq.symm (Nat.div_mul_cancel hq_div)
  obtain ⟨m, hm, p, hp, h⟩ := this
  have := divisibilitas_generalis a m p
  rw [←h] at this
  absurd h_prime
  apply Nat.not_prime_of_dvd_of_lt this (Nat.succ_lt_succ (a.pow_pos ha.le))
  field_simp only [lt_mul_right,h,a.pow_lt_pow_right,Nat.succ_lt_succ,Nat.lt_add_of_pos_left]

/-!
Neque tamen ex hoc potest concludi $a^{2^m}+1$ semper exhibere numerum primum, quicquid sit $a$;
primo enim perspicuum est, si $a$ sit numerus impar, istam formam divisorem habiturum $2$.
-/
theorem exception_impar (a m : ℕ) (h_odd : Odd a) :
    2 ∣ (a ^ (2 ^ m) + 1) := by
  exact (h_odd.pow.add_one).two_dvd



/-!
Deinde quoque, etiamsi $a$ denotet numerum parem, innumeri tamen dantur casus, quibus numerus
compositus prodit. Ita haec saltem formula $a^2+1$ potest dividi per $5$, quoties est $a=5b\pm3$,
...
-/
example (b : ℕ) : 5 ∣ ((5 * b + 3) ^ 2 + 1) := by
  use b * (b * 5 + 6) + 2
  ring

example (b : ℤ) : 5 ∣ ((5 * b - 3) ^ 2 + 1) := by
  use b * (b * 5 - 6) + 2
  ring

/-!
... et $30^2+1$ potest dividi per $17$,...
-/
example : 17 ∣ (30 ^ 2 + 1) := by decide

/-!
... et $50^2+1$ per $41$.
-/
example :  41 ∣ (50 ^ 2 + 1) := by decide

/-!
Simili modo $10^4+1$ habet divisorem $73$, ...
-/
example : 73 ∣ (10 ^ 4 + 1) := by decide

/-!
... $6^8+1$ habet divisorem $17$ ...
-/
example : 17 ∣ (6 ^ 8 + 1) := by decide

/-!
.. et $6^{128}+1$ est divisibilis per $257$.
-/
example : 257 ∣ (6 ^ 128 + 1) := by norm_num

/-!
At huius formae $2^m+1$ quantum ex tabulis numerorum primorum, quae quidem non ultra 100000
extenduntur, nullus detegitur casus, quo divisor aliquis locum habeat.
-/
theorem observatio_tabularum (k : ℕ) (hk_bound : k < 100000) :
    (∃ n, k = 2 ^ (2 ^ n) + 1) → k.Prime := by
  rintro ⟨n, rfl⟩
  have : 2 ^ (2 ^ n) < 2 ^ (2 ^ 5) := by omega
  have h_n_lt_5 : n < 5 := by
    have := (Nat.pow_lt_pow_iff_right (by decide)).mp this
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  interval_cases n <;> norm_num

/-!
Sed nescio, quo fato eveniat, ut statim sequens, nempe $2^{2^5} + 1$, cesset esse numerus primus.
Observavi enim his diebus longe alia agens posse hunc numerum dividi per $641$, ut cuique
tentanti statim patebit.
-/
theorem sequens_non_primus : ¬ (2 ^ (2 ^ 5) + 1).Prime := by
  rw [Nat.prime_def_lt]
  push_neg
  norm_num
  use 641
  norm_num

/-!
Est enim $2^{2^5} + 1 = 2^{32} + 1 = 4294967297$.
-/
example : 2 ^ (2 ^ 5) + 1 = 4294967297 := by norm_num

/-!
Ex quo intelligi potest theorema hoc etiam in aliis, qui sequuntur, casibus fallere et hanc
ob rem problema de inveniendo numero primo quovis dato maiore etiam nunc non esse solutum.
-/
theorem fallacia_conjecturae : ¬ (∀ n, (2 ^ (2 ^ n) + 1).Prime) := by
  push_neg
  use 5
  exact sequens_non_primus

/-!
## Theorema 1

Si fuerit $n$ numerus primus, omnes potentia exponentis $n-1$ per $n$ divisa vel nihil vel unitatem
relinquit.
-/
theorem theorema_1 (a n : ℕ) (hn : n.Prime) :
    ((a ^ (n - 1)) : ZMod n) ∈ ({0, 1} : Finset (ZMod n)) := by
  sorry

/-!
## Theorema 2

Manente $n$ numero primo omnis potentia, cuius exponens est $n^{m-1}(n-1)$, divisa per $n^m$ vel $0$
vel $1$ relinquit.
-/
theorem theorema_2 (a n m : ℕ) (hn : n.Prime) (hm : m > 0) :
    (a ^ (n ^ (m - 1) * (n - 1)) : ZMod (n ^ m)) ∈ ({0, 1} : Finset (ZMod (n ^ m))) := by
  sorry

/-!
## Theorema 3

Sint $m, n, p, q$ etc. numeri primi inaequales, sitque $A$ minimus communis dividuus eorum unitate
minutorum, puta ipsorum $m-1, n-1, p-1, q-1$ etc.; his positis dico omnem potentiam exponentis $A$
ut $a^A$ diuisam per $mnpq$ etc. vel $0$ vel $1$ relinquere, nisi $a$ dividi possit per aliquem
horum numerorum $m, n, p, q$ etc.
-/
theorem theorema_3 (primes : Finset ℕ) (h_primes : ∀ p ∈ primes, p.Prime) (a : ℕ) :
    -- minimus communis dividuus eorum unitate minutorum, puta ipsorum $m-1, n-1, p-1, q-1$ etc.
    let A := (primes.toList.map (fun n => n - 1)).toFinset.lcm id
    -- $mnpq$ etc.
    let P := ∏ p ∈ primes, p
    (∀ p ∈ primes, ¬ p ∣ a) → ((a ^ A) : ZMod P) ∈ ({0, 1} : Finset (ZMod P)):= by
  sorry

/-!
## Theorema 4

Denotante $2n+1$ numerum primum poterit $3^n+1$ dividi per $2n+1$, si sit vel $n=6p+2$ vel
$n=6p+3$; at $3^n-1$ dividi poterit per $2n+1$, si sit vel $n=6p$ vel $n=6p-1$.
-/
theorem theorema_4 (n : ℕ) (h_prime : (2 * n + 1).Prime) :
    ((∃ p, n = 6 * p + 2 ∨ n = 6 * p + 3) → 2 * n + 1 ∣ 3 ^ n + 1) ∧
    ((∃ p, n = 6 * p ∨ n = 6 * p - 1) → 2 * n + 1 ∣ 3 ^ n - 1) := by
  sorry

/-!
## Theorema 5

$3^n+2^n$ potest dividi per $2n+1$, si sit $n=$ vel $12p+3$ vel $12p+5$ vel $12p+6$ vel $12p+8$.
Atque $3^n-2^n$ potest dividi per $2n+1$, si sit $n=$ vel $12p$ vel $12p+2$ vel $12p+9$ vel
$12p+11$.
-/
theorem theorema_5 (n : ℕ) (h_prime : (2 * n + 1).Prime) :
    ((∃ p, n = 12 * p + 3 ∨ n = 12 * p + 5 ∨ n = 12 * p + 6 ∨ n = 12 * p + 8) →
    2 * n + 1 ∣ 3 ^ n + 2 ^ n) ∧
    ((∃ p, n = 12 * p ∨ n = 12 * p + 2 ∨ n = 12 * p + 9 ∨ n = 12 * p + 11) →
    2 * n + 1 ∣ 3 ^ n - 2 ^ n) := by
  sorry

/-!
## Theorema 6

Sub iisdem conditionibus, quibus $3^n+2^n$, poterit etiam $6^n+1$ dividi per $2n+1$; atque
$6^n-1$ sub iisdem, quibus $3^n-2^n$.
-/
theorem theorema_6 (n : ℕ) (h_prime : (2 * n + 1).Prime) :
    ((∃ p, n = 12 * p + 3 ∨ n = 12 * p + 5 ∨ n = 12 * p + 6 ∨ n = 12 * p + 8) →
    2 * n + 1 ∣ 6 ^ n + 1) ∧
    ((∃ p, n = 12 * p ∨ n = 12 * p + 2 ∨ n = 12 * p + 9 ∨ n = 12 * p + 11) →
    2 * n + 1 ∣ 6 ^ n - 1) := by
  sorry

end Euler.SeriesPrima.Volumen2.E26
