# B₂ — proposta analitica di sostituzione via QRH 7/8 e correlazioni quadratiche

**Direzione di ricerca:** Maicol Borghetti — laboratorio RH, Teoria dello Zero (@maicborg)  
**Sviluppo e audit matematico:** assistenza GPT-6, 22 novembre 2026  
**Stato epistemico:** PROPOSTA DI DIMOSTRAZIONE SU CARTA, non compilata in Lean, non certificata come originale, non prova di RH. La verifica della stima uniforme PNT(7/8) e il porting nel progetto Alpöge sono ancora aperti.

## 0. Obiettivo concreto, non il vecchio budget B₂

Nel codice Alpöge, commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, il teorema `QH.meanSqK` garantisce

```lean
MeanSq C ((Y ^ K) ^ 400) (PPset m₀ a₀ U) (Set.Icc Y (Y ^ K))
```

dove

```lean
def S (Z y : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊Z⌋₊, ((cN y n : ℝ) : ℂ) * κ n *
    ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

def cN (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / n)
```

e `MeanSq` equivale a

```
∀ y∈[Y,Y^K], ∀ κ con |κ(n)|≤1:
∑_{q∈P} |S(Z,y,q,κ)|² ≤ C y log(y) |P|.
```

Attualmente la prova usa `twistK` (356 righe), `meanSq_abs`, `RR_le`, diversi lemmi su Jacobi e l'analisi dell'eventuale carattere eccezionale `nstar`. **Vogliamo un rimpiazzo di questo input analitico**, non soltanto del conteggio finale già certificato in `B2Budget.lean`.

## 1. Input forte e non circolare da OpenAI

Per tutti i caratteri Dirichlet, inclusi quelli di conduttore variabile, il risultato OpenAI QRH(7/8) esclude gli zeri non banali di parte reale **strettamente maggiore** di 7/8; per i principali si tratta separatamente il polo in s=1.

Dalla formula esplicita classica, dal conteggio uniforme degli zeri e dalla simmetria funzionale si dovrebbe formalizzare il seguente lemma quantitativo **PNT78**:

```
Per ogni carattere non principale η modulo M≥1 e x≥3,
| ∑_{p≤x} η(p) | ≤ C x^(7/8) (log(Mx))^A,
```

per un esponente assoluto fissato A (ad es. A=4) e costante assoluta C. Si chiede uniformità per M≤x, sufficiente qui. Per i principali, la somma è `Li(x)` più un errore della stessa grandezza. Questa è una **conseguenza standard attesa** del teorema 7/8 attraverso la formula esplicita, ma non è ancora importata come theorem Lean nel nostro repo. Gli zeri imprimitive dovuti ai fattori di Eulero mancanti vanno trattati separatamente.

Riferimenti di metodo: Montgomery–Vaughan, *Multiplicative Number Theory*; [Counting zeros and the explicit formula for ψ(x,χ)](https://kokunoyumeto.github.io/open-math-courses-public/courses/NT-DIRL/NT-DIRL-08.html); [Kedlaya, Error bounds for primes in arithmetic progressions](https://kskedlaya.org/ant/chapter-11.html).

**Non postulare PNT78 nel risultato finale:** o dimostrarlo da OpenAI QRH(7/8) + formula esplicita verificata, oppure etichettare tutta la catena come condizionale. La nota OpenAI 11/12 include già una conseguenza sulla distribuzione dei primi; da controllare in prior art anche per la versione 7/8.

## 2. La scala particolarmente favorevole di Alpöge

Sia `m=m₀`, `P=PPset m a U`, `Z=(Y^K)^400`, `1≤K`, `0<ε≤1/4`. Dal predicato Alpöge `admitted ε Y U m a` si ha:

```
(1/4) log²(Y) log(m) ≤ log(U),
Y^(ε/6) ≤ log(U),
log(U) ≤ Y^(ε/5) log²(Y),
8 | m, gcd(a,m)=1.
```

Quindi

```
log(m) ≤ 4 Y^(ε/5),
log(m Z²) / log(U) ≤ 4/log²(Y) + 800 K log(Y)/Y^(ε/6) → 0.
```

Per ogni δ>0 fissato, da un certo Y₀(ε,K,δ) vale `m Z² ≤ U^δ`. Scegliamo δ=1/64. In particolare, per ogni `q∈P`, `q>√U>Z`, quindi nessuna potenza prima nella somma è divisibile da q.

Se PNT78 vale uniformemente, tramite ortogonalità dei caratteri modulo m segue:

```
|P| ≥ c U / (φ(m) log U)
```

per Y abbastanza grande, perché m≤U^(1/64) e 7/8+1/64<1. Il limite inferiore sul numero dei primi non richiede qui un ulteriore Siegel–Walfisz con eccezioni.

## 3. Identità esatta: potenze prime pari e dispari

Dato che Λ(n) è zero salvo n=p^k, per ogni q∈P e κ con |κ(n)|≤1 definiamo:

```
b_p(y,Z,κ) = ∑_{k≥1 dispari, p^k≤⌊Z⌋} cN(y,p^k) κ(p^k).
E(y,Z,κ) = ∑_{k≥2 pari, p^k≤⌊Z⌋} cN(y,p^k) κ(p^k).
```

Per q>Z primo, il simbolo di Jacobi soddisfa `(p^k/q)=(p/q)^k`, e per k pari vale 1. Inoltre, se p|m, dato che 8|m e q≡a(mod m), il segno `(p/q)` è costante per reciprocità quadratica (p=2 usa q mod 8). Pertanto

```
S(Z,y,q,κ) = A(y,Z,κ,m,a) + ∑_{p≤Z, p∤m} b_p(y,Z,κ) (p/q),

A = E + ∑_{p|m} b_p (p/q₀), per un qualunque q₀∈P.
```

**Questa identità è esatta**, non richiede QRH né stime asintotiche. Per P non vuoto la definizione di A è indipendente dalla scelta di q₀.

## 4. Ortogonalità approssimata lungo i primi del PPset

Per primi distinti `p,r≤Z` con p,r∤m, si ha per q∈P:

```
(p/q)(r/q) = (pr/q) = χ_D(q),
```

dove `χ_D` è un carattere quadratico non principale di conduttore divisore di 4pr. Dato `8|m` e `p,r∤m`, il carattere `χ_D ψ` resta non principale per ogni carattere ψ modulo m (il suo conduttore ha fattori primi p e r assenti da m).

Espandendo `1_{q≡a(m)}` per ortogonalità dei caratteri modulo m e applicando PNT78, otteniamo la stima di correlazione uniforme

```
|∑_{q∈P} (p/q)(r/q)|
≤ E_U := C U^(7/8) log^A(U m Z²)       (p≠r, p,r∤m).
```

Per p=r, ogni simbolo ha quadrato 1, perché q>Z≥p.

Questa stima è il **lemma-ponte matematico decisivo** ancora da rendere formale: qui serve verificare con precisione i moduli di ogni carattere, i termini dei principali, gli endpoint x=√U e x=U, la dipendenza assoluta delle costanti e la compatibilità con i caratteri imprimitive.

## 5. Riduzione di meanSqK a tre stime elementari

Pongo `T_q=∑_{p∤m}b_p(p/q)` e uso `|A+T|²≤2|A|²+2|T|²`.

L'espansione del quadrato e la stima uniforme di correlazione danno

```
(1/|P|) ∑_{q∈P}|S_q|²
≤ 2 |A|² + 2∑_{p∤m}|b_p|²
  + 2 (E_U/|P|) (∑_{p∤m}|b_p|)².         (★)
```

Per `Y≤y≤Y^K`, `Z=Y^(400K)`, con `|κ|≤1`, le stime aritmetiche classiche da Chebyshev `θ(t)≪t` e sommazione parziale forniscono, **uniformemente in Z**:

```
(i)  ∑_{p≤Z}|b_p|² ≪ y log y;
(ii) ∑_{p≤Z}|b_p|   ≪ y (1+log Z);
(iii) |E| ≪ √y;
(iv) ∑_{p|m}|b_p| ≪ (log m)(1+log y).
```

Traccia delle prove:
- (i) il contributo k=1 soddisfa `∑_p (log p)² min(1,y/p)² ≪ y log y`, per θ(t)≪t e integrazione per parti; la coda k≥3 è `O(y^(1/3)log²y)` nel quadrato, quindi assorbita;
- (ii) `∑_{n≤Z}Λ(n)min(1,y/n)≪y(1+log Z)`;
- (iii) prime potenze pari: contributo delle potenze quadrate `O(√y)` da θ(t)≪t, potenze superiori `O(y^(1/4)log y)`, assorbito per y grande;
- (iv) per ciascun p|m la somma sulle potenze p^k fino a y pesa al più `log y`; la coda geometrica pesa `O(log p)`; si usa `ω(m)≪log m`.

Dal limite `log m≤4Y^(ε/5)` e `ε≤1/4`, il contributo (iv) ha quadrato `≪_{K}Y^(2ε/5)log²Y≪y`. Pertanto `|A|²≪y` (per Y sufficientemente grande dipendente da ε,K).

Infine, da `φ(m)≤m≤U^(1/64)` e dal limite inferiore su |P|,

```
E_U/|P| ≪ U^(-7/64) log^(A+1)U
```

e per `log U≥Y^(ε/6)`, ogni fattore `Y^K` e `log Z` è dominato da questa potenza negativa di U. Il terzo termine in (★) è `o(y log y)`, uniformemente nell'intervallo `y∈[Y,Y^K]`.

Segue il candidato **meanSqK-QRH78**:

```
Per 0<ε≤1/4 e K≥1, esistono C>0 assoluto e Y₀(ε,K),
tali che per ogni Y≥Y₀, U,m,a ammessi, ogni y∈[Y,Y^K],
ogni κ:ℕ→ℂ con |κ(n)|≤1,

∑_{q∈PPset(m,a,U)}
 |S((Y^K)^400,y,q,κ)|²
≤ C y log y · |PPset(m,a,U)|.
```

**Conseguenza potenziale:** usa una conseguenza quantitativa di OpenAI QRH78 e manipolazioni delle potenze prime, senza l'intera catena `twistK`/carattere eccezionale `nstar`, senza servirsi della condizione aggiuntiva `hp` del vecchio `meanSqK`. Non implica ancora che il modulo originale `QH.stage` ricompili e che la dipendenza downstream scompaia.

## 6. Test numerico di integrità algebrica (NON prova asintotica)

Prova indipendente Python/SymPy con U=100000, m=24, a=1, y=30, Z=100; P=1176 primi q∈(√U,U] con q≡1(mod24); κ(n)=exp(0.31 i n). Sono comparati direttamente la definizione della somma su Λ(n) con segno di Jacobi e la decomposizione in A+∑b_p(p/q).

- errore assoluto massimo dell'identità sulle 1176 istanze: 9.06 ×10^(-15);
- media dei quadrati diretta: 158.5635684;
- termine diagonale teorico `|A|²+∑|b_p|²`: 158.0132791;
- massima correlazione assoluta campionaria fra due primi distinti p,r≤Z: 0.0952381 (p=17,r=83).

**Limite:** U=100000 non soddisfa necessariamente i regimi asintotici `admitted`. Questo test verifica soltanto identità e grandezze di correlazione a scala piccola, non il nuovo theorem né l'esponente 7/8.

## 7. Falsificatori e gate obbligatori

F1. PNT78 dalla QRH(7/8) OpenAI **non è davvero uniforme** per tutti i caratteri/conduttori M≤U^(1/64), oppure il costo per gli imprimitive non è controllato: la proposta fallisce.

F2. Esiste `p≠r, p,r∤m` tale che `χ_D ψ` diventa principale modulo m·4pr, oppure la parità Jacobi non è costante per p|m: la decomposizione/correlazione è sbagliata.

F3. Una stima aritmetica (i)-(iv) perde un fattore crescente di `log y` non assorbibile da `C y log y`: manca la stessa `MeanSq` usata in B₂.

F4. Le costanti o le soglie Y₀ dipendono surrettiziamente da U, m, a, y, κ oltre ε,K: non sostituisce `meanSqK`.

F5. Il theorem 7/8 o la formula esplicita usati già dipendono da un'ipotesi equivalente al risultato finale nel contesto Lean concreto: circolarità/assenza di import verificato.

F6. Il percorso è già disponibile nella letteratura o in una semplificazione pubblicata: nessuna novità originale rivendicabile.

**Gate:** G0 sorgenti verificate, prior art incompleto; G1 identità aritmetica derivata e testata numericamente; G2 stima quadratica derivata *assumendo PNT78 con uniformità esatta*; G3 PNT78 ottenuta in Lean da OpenAI + formula esplicita NON FATTO; G4 QH.stage compilato con rimpiazzo NON FATTO; G5 audit indipendente NON FATTO.

### Fonti primarie

- [OpenAI, theorem 7/8 in Lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean).
- [Alpöge PrimeSetTwoBounds.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean) (S, admitted, MeanSq).
- [Alpöge cN](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean).
- [Alpöge meanSqK.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean).
- [Alpöge BadShare.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean).
- [OpenAI 11/12 paper: prime progressions corollary](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex).
