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
Considerabo nunc etiam formulam $2^n - 1$, quae, quoties $n$ non est numerus primus, habet
divisores, ...
-/
theorem si_n_compositus_mersennus_compositus (n : ℕ) (h : ¬ n.Prime) (hn : 1 < n) :
    ¬ (2 ^ n - 1).Prime := by
  refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
  · exact (2).le_pred_of_lt (lt_self_pow₀ (by decide) hn)
  · have : ∃ x > 1, ∃ y > 1, x < n ∧ y < n ∧ n = x * y := by
      sorry
    obtain ⟨x, hx1, y, hy1, hxn, hyn, h_prod⟩ := this
    use 2^x - 1
    sorry


/-!
... neque tantum $2^n - 1$, sed etiam $a^n - 1$.
-/
theorem si_n_compositus_compositus (n a : ℕ) (h : ¬ n.Prime) (hn : 1 < n) (ha : 1 < a):
    ¬ (a ^ n - 1).Prime := by
  refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
  · exact (Nat.lt_pow_self ha).le_pred.trans' hn
  · have : ∃ x > 1, ∃ y > 1, x < n ∧ y < n ∧ n = x * y := by
      sorry
    obtain ⟨x, hx1, y, hy1, hxn, hyn, h_prod⟩ := this
    use a^x - 1
    sorry


/-!
Sed si $n$ sit numerus primus, videri posset etiam $2^n - 1$ semper talem exhibere: hoc tamen
asseverare nemo est ausus, cum tam facile potuisset refelli.
-/
theorem non_omnis_mersennus_primus : ¬ (∀ n, n.Prime → (2 ^ n - 1).Prime) := by
  push_neg
  use 11
  norm_num

/-!
Namque $2^{11} - 1$ i. e. $2047$ divisores habet $23$ ...
-/
example : (2 ^ 11 - 1).primeFactors = {23, 89} := by
  simp [Nat.primeFactors]

/-!
... et $89$ et $2^{23} - 1$ dividi potest per $47$.
-/
example : 47 ∣ (2 ^ 23 - 1) := by norm_num

/-!
Video autem Cel. Wolfium non solum hoc in Elem. Matheseos editione altera non advertisse, ubi
numeros perfectos investigat atque $2047$ inter primos numerat, sed etiam $511$ seu $2^9 - 1$
pro tali habet, cum tamen sit divisibilis per $2^3 - 1$ i.e. $7$.
-/
theorem errores_wolfii : ¬ (2047).Prime ∧ ¬ (511).Prime ∧ (2^3 - 1) ∣ (2^9 - 1) := by
  norm_num

/-!
Dat autem $2^{n-1}(2^n - 1)$ numerum perfectum, quoties $2^n - 1$ est primus, ...
-/
theorem generatio_perfecti (n : ℕ) (h_prime : (2 ^ n - 1).Prime) :
    ((2 ^ (n - 1) * (2 ^ n - 1))).Perfect := by
  constructor
  · sorry
  · exact (Nat.mul_pos (n - 1).two_pow_pos) (h_prime).pos

/-!
... debet ergo etiam $n$ esse numerus primus.
-/
theorem necessitas_exponentis_primi (n : ℕ) (h_prime : (2 ^ n - 1).Prime) (hn : n ≠ 1) :
    n.Prime := by
  by_contra h_not_prime
  absurd h_prime
  apply si_n_compositus_mersennus_compositus n
  · exact h_not_prime
  · exact hn.symm.lt_of_le (by cases n with | zero => contradiction | succ n => omega)

/-!
Inveni autem hoc semper fieri, si sit $n = 4m - 1$, atque $8m - 1$ fuerit numerus primus,
tum enim $2^n - 1$ semper poterit dividi per $8m - 1$.
-/
theorem regula_divisoris_mersenni (m n : ℕ) (hm : m ≥ 1) (hn : n = 4 * m - 1)
    (h_prime : (8 * m - 1).Prime) : (8 * m - 1) ∣ (2 ^ n - 1) := by
  let p := 8 * m - 1
  have : n = (p - 1) / 2 := by
    omega
  have : Fact (p.Prime) := { out := h_prime }
  have : 2^n = ((legendreSym p 2) : ZMod p) := by
    simp only [legendreSym.eq_pow, Int.cast_ofNat]
    exact (congr_arg _) (by valid)
  have : 2^n = (1 : ZMod p) := by
    rw [this,legendreSym.at_two]
    · rw [ZMod.χ₈_nat_eq_if_mod_eight]
      norm_num [(by omega : p%2 ≠ 0 ∧ p%8 = 7)]
    · omega
  field_simp only [push_cast, sub_self, this, ←CharP.cast_eq_zero_iff (ZMod p),Nat.cast_pred]


/-!
Hinc excludendi sunt casus sequentes: 11, 23, 83, 131, 179, 191, 239, etc. qui numeri pro $n$
substituti reddunt $2^n - 1$ numerum compositum.
-/
theorem casus_excludendi :
    ¬ (2 ^ 11 - 1).Prime ∧
    ¬ (2 ^ 23 - 1).Prime ∧
    ¬ (2 ^ 83 - 1).Prime ∧
    ¬ (2 ^ 131 - 1).Prime ∧
    ¬ (2 ^ 179 - 1).Prime ∧
    ¬ (2 ^ 191 - 1).Prime ∧
    ¬ (2 ^ 239 - 1).Prime := by
  norm_num

/-!
Neque tamen reliqui numeri primi omnes loco $n$ positi satisfaciunt, sed plures insuper
excipiuntur; sic observavi $2^{37} - 1$ dividi posse per $223$...
-/
theorem divisio_37 : 223 ∣ (2 ^ 37 - 1) := by norm_num

/-!
... $2^{43} - 1$ per $431$...
-/
theorem divisio_43 : 431 ∣ (2 ^ 43 - 1) := by norm_num

/-!
... $2^{29} - 1$ per $1103$...
-/
theorem divisio_29 : 1103 ∣ (2 ^ 29 - 1) := by norm_num

/-!
... $2^{73} - 1$ per $439$, omnes tamen excludere non est in potestate.
-/
theorem divisio_13 : 439 ∣ (2 ^ 73 - 1) := by norm_num

/-!
Attamen asserere audeo praeter hos casus notatos, omnes numeros primos minores quam 50, et forte
quam 100, efficere $2^{n-1}(2^n - 1)$ esse numerum perfectum, sequentibus numeris pro $n$ positis,
1, 2, 3, 5, 7, 13, 17, 19, 31, 41, 47, unde 11 proveniunt numeri perfecti.
-/
private def indices_euleri : List ℕ := [1, 2, 3, 5, 7, 13, 17, 19, 31, 41, 47]

example : indices_euleri.length = 11 := by decide

/-!
[Eulerus hic errat: 41 et 47 numeros compositos generant!].
-/
theorem refutatio_assertionis_de_41_et_47 :
    ¬ (2 ^ 41 - 1).Prime ∧ ¬ (2 ^ 47 - 1).Prime := by norm_num

theorem assertio_euleri : ∀ n ∈ indices_euleri, (n ∈ [1, 41, 47] ∨ (2 ^ n - 1).Prime) := by
  unfold indices_euleri
  intro n h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num


/-!
Deduxi has observationes ex theoremate quodam non ineleganti, cuius quidem demonstrationem quoque
non habeo, verum tamen de eius veritate sum certissimus.
Theorema hoc est: $a^n - b^n$ semper potest dividi per $n+1$, si $n+1$ fuerit numerus primus atque
$a$ et $b$ non possint per eum dividi...
-/
theorem non_inelegans (a b n : ℕ) (h_prime : Fact (n + 1).Prime)
    (ha : ¬ (n + 1) ∣ a) (hb : ¬ (n + 1) ∣ b) :
    (n + 1) ∣ (a ^ n - b ^ n) := by
  let p := n + 1
  have ha_pow : a ^ n % p = 1 := by
    erw [← ZMod.val_natCast, Nat.cast_pow, ZMod.pow_card_sub_one_eq_one
      (by apply ha.comp (CharP.cast_eq_zero_iff _ _ _).1), ZMod.val_one]
  have hb_pow : b ^ n % p = 1 := by
    erw [← ZMod.val_natCast, Nat.cast_pow, ZMod.pow_card_sub_one_eq_one
      (by apply hb.comp (CharP.cast_eq_zero_iff _ _ _).1), ZMod.val_one]
  have : a ^ n ≡ b ^ n [MOD p] := by rw [Nat.ModEq, ha_pow, hb_pow]
  exact (p.dvd_of_mod_eq_zero) (Nat.sub_mod_eq_zero_of_mod_eq this)


/-!
... eo autem difficiliorem puto eius demonstrationem esse, quia non est verum, nisi $n+1$ sit
numerus primus.
-/
theorem necessitas_primitatis (n : ℕ) (h_not_prime : ¬ (n + 1).Prime) (hn : 0 < n):
    ¬ (∀ a b : ℕ, ¬ (n + 1) ∣ a → ¬ (n + 1) ∣ b → (n + 1) ∣ (a ^ n - b ^ n)) := by
  sorry

/-!
Ex hoc statim sequitur $2^n - 1$ semper dividi posse per $n+1$, si fuerit $n+1$ numerus primus, ...
-/
theorem corollarium_non_inelegans (n : ℕ) (h_prime : Fact (n + 1).Prime) (h_ne_two : n + 1 ≠ 2) :
    (n + 1) ∣ (2 ^ n - 1) := by
  have := non_inelegans 2 1 n h_prime
  simp only [Nat.dvd_one, Nat.add_eq_right, one_pow] at this
  apply this
  · rwa [Nat.prime_dvd_prime_iff_eq h_prime.1 (by decide)]
  · intro h
    rw [h] at h_prime
    tauto

/-!
... seu, cum omnis primus sit impar praeter $2$ hicque ob conditiones theorematis, quia est $a=2$,
non possit adhiberi,...
-/
theorem exclusio_binarii (n : ℕ) (h_prime : (n + 1).Prime) (h_two : n + 1 = 2) :
    ¬ (¬ (n + 1) ∣ 2) := by
  rw [h_two]
  simp


/-!
... poterit $2^{2m} - 1$ semper dividi per $2m+1$ si $2m+1$ sit numerus primus.
-/
theorem corollarium_non_inelegans' (m : ℕ) (h_prime : Fact (2 * m + 1).Prime) :
    (2 * m + 1) ∣ (2 ^ (2 * m) - 1) := by
  have := non_inelegans 2 1 (2 * m) h_prime
  simp at this
  apply this
  · use h_prime.1.ne_one.comp ( Odd.coprime_two_right ⟨m, rfl⟩).eq_one_of_dvd
  · intro h
    rw [h] at h_prime
    tauto



/-!
Quare etiam vel $2^m + 1$ vel $2^m - 1$ dividi poterit per $2 * m + 1$.
Deprehendi autem $2^m + 1$ posse dividi, si fuerit $m = 4p + 1$ vel $4p + 2$;...
-/
theorem conditio_divisibilitatis_plus (m : ℕ) (h_prime : (2 * m + 1).Prime) :
    (∃ p, m = 4 * p + 1 ∨ m = 4 * p + 2) → (2 * m + 1) ∣ (2 ^ m + 1) := by
  sorry

/-!
... at $2^m - 1$ habebit divisorem $2m + 1$, si $m = 4p$ vel $4p - 1$.
-/
theorem conditio_divisibilitatis_minus (m : ℕ) (h_prime : (2 * m + 1).Prime) :
    (∃ p, m = 4 * p ∨ m = 4 * p - 1) → (2 * m + 1) ∣ (2 ^ m - 1) := by
  sorry



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
