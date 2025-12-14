import Mathlib

/-!
# Observationes de theoremate quodam Fermatiano aliisque ad numeros primos spectantibus
Commentatio 26 indices Enestroemiani

Commentarii academiae scientiarum Petropolitanae 6 (1732/3), 1738, p. 103-107
-/

namespace Euler.SeriesPrima.Volumen2.E26

open Nat

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
