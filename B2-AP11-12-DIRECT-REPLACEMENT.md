# B₂: sostituzione diretta via il corollario OpenAI 11/12 sui primi in progressioni

**Data:** 22 novembre 2026. **Direzione scientifica:** Maicol Borghetti, laboratorio RH. **Audit/derivazione:** GPT-6.  
**Tipo:** proposta analitica dettagliata con input teorematico dichiarato, non ancora dimostrazione Lean di `QH.meanSqK` né prova originale di RH.  
**Provenienza:** Alpöge source `CocoSgt/riemann-hypothesis-lean` commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, OpenAI `The Quasi-Riemann Hypothesis` 11/12, 5 ottobre 2026, `paper2.tex` Corollary 1.2.  
**Relazione con V1:** [B2-Q78-QUADRATIC-CORRELATION-RESEARCH.md](B2-Q78-QUADRATIC-CORRELATION-RESEARCH.md) usava un lemma ipotetico PNT uniforme per caratteri; questa V2 evita tale lemma utilizzando **direttamente** il corollario scritto di OpenAI in progressioni. Non sovrascrive la V1.

## 1. Teorema esterno concreto, verificato nel testo della fonte

Nel sorgente primario OpenAI https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex (righe del file GitHub 2288–2311) il Corollario 1.2 afferma: con `Li₂(x)=∫₂ˣ dt/log t` per `x≥2`, `1≤M≤x` e `gcd(b,M)=1`,

```
| π(x;M,b) − Li₂(x)/φ(M) | ≤ C_AP x^(11/12) log(x)
```

con costante assoluta effettiva `C_AP`.

È un **risultato enunciato nella fonte originale**, non una prova che abbiamo importato nel nostro Lean: il paper rinvia a una formula esplicita classica per la derivazione. Questo è il nostro input PNT-AP. Non basta scrivere `hAP` come ipotesi e chiamare il ponte 'certificato'.

## 2. Uniformità nel regime esatto Alpöge

Siano `0<ε≤1`, `K≥1`, `Y≥Y₀(ε,K)`, `m=m₀`, `a=a₀`, `Z=(Y^K)^400=Y^(400K)`, `P=PPset(m,a,U)`.

Dalla struttura `admitted ε Y U m a` del codice Alpöge:

```
8|m, gcd(a,m)=1,
(1/4) (log Y)² log m ≤ log U,
Y^(ε/6) ≤ log U.
```

Per `Y>e`, ne segue

```
log m ≤ 4 log U/(log Y)².
log (m Z²)/log U ≤ 4/(log Y)² + 800K log Y / Y^(ε/6).
```

Il lato destro tende a zero per Y→∞ **uniformemente in U,m,a**. Per Y sufficientemente grande è ≤1/64. Quindi

```
m Z² ≤ U^(1/64).
```

Dato `log U≥Y^(ε/6)`, anche `Z<√U`, e quindi tutti i q∈P sono diversi dai primi p≤Z e coprimi con m.

## 3. CRT + reciprocità: correlazione di Jacobi come somme AP

Siano p,r≤Z due primi distinti non divisori di m. Scegliamo `M=mpr` (siccome 8|m la classe q modulo 4 resta fissata). Per q∈P:

```
(p/q)(r/q) = σ_{p,r}(q mod M)
```

con `σ∈{−1,+1}` sui residui invertibili q mod M. Per reciprocità quadratica, modulo un segno costante imposto da `q≡a (mod 8)`, è il prodotto dei due simboli di Legendre `(q/p)(q/r)`.

Le classi ammissibili sono

```
R_{p,r}={b mod M : gcd(b,M)=1, b ≡ a (mod m)}.
```

Il teorema cinese del resto identifica R con `(ℤ/pℤ)^× × (ℤ/rℤ)^×`; perciò

```
|R_{p,r}|=(p−1)(r−1) ≤ pr,
∑_{b∈R_{p,r}}σ_{p,r}(b)=0.
```

**Nota:** L'uguaglianza è dovuta all'ortogonalità del carattere di Legendre in una variabile. È l'identità algebrica cruciale da formalizzare (CRT e reciprocità) senza introdurre ipotesi GRH.

Per `x∈{U,√U}`, la formula AP del §1 fornisce

```
| ∑_{b∈R} σ(b) π(x;M,b) |
  = | ∑_{b∈R} σ(b)[π(x;M,b)−Li₂(x)/φ(M)] |
  ≤ |R| C_AP x^(11/12) log x
  ≤ pr C_AP U^(11/12) log U.
```

Sottraendo i due endpoint e usando `M=mpr≤mZ²≤U^(1/64)<√U`:

```
|∑_{q∈P} (p/q)(r/q)| ≤ 2 C_AP pr U^(11/12) log U
                              ≤ 2 C_AP Z² U^(11/12) log U.     (CROSS)
```

Tutto il trasferimento usa **solo PNT-AP 11/12, CRT, reciprocità quadratica, ortogonalità, triangolare**. Non richiede di ricostruire la formula esplicita né uno specifico teorema PNT in caratteri imprimitive.

## 4. Grandezza del set P

Applicando il medesimo corollario 11/12 al modulo m nei due endpoint:

```
|P| ≥ [Li₂(U)−Li₂(√U)]/φ(m) − 2 C_AP U^(11/12) log U.
```

Con `φ(m)≤m≤U^(1/64)` e `Li₂(U)−Li₂(√U) ≥ c U/log U` per U grande,

```
|P| ≥ c' U/[m log U]   (c'>0 assoluta, per Y≥Y₀).
```

Da (CROSS):

```
max_{p≠r≤Z,,p,r∤m}
 |∑_{q∈P}(p/q)(r/q)|/|P|
 ≤ C'' m Z² U^(−1/12)(log U)²
 ≤ C'' U^(−13/192)(log U)².                            (RATIO)
```

L'esponente `−13/192` è esattamente `−1/12 + 1/64`, positivo come risparmio. Questa stima è uniforme in m,a,p,r,κ,y e U soggetti ad `admitted`, per ε,K fissati.

## 5. Identità delle potenze prime e bound sui pesi

Con `c_y(n)=Λ(n) min(1,y/n)`, `|κ(n)|≤1`, separare le potenze pari e quelle dispari. Per q>Z:

```
S(Z,y,q,κ)=A(y,Z,κ,m,a)+∑_{p≤Z,,p∤m} b_p(y,Z,κ) (p/q),
b_p=∑_{k≥1 dispari,,p^k≤Z} c_y(p^k) κ(p^k),
A=∑_{p,k pari} c_y(p^k) κ(p^k) +
  ∑_{p|m,k dispari} c_y(p^k) κ(p^k) (p/q₀),
```

dove per p|m il simbolo (p/q) è costante sulla classe q≡a (mod m), quindi q₀ è un qualunque primo di P (P nonvuoto per Y grandi). Decomposizione **esatta**.

Da Chebyshev `∑_{p≤t}log p≪t` e sommazione parziale, richiedendo dimostrazioni esplicite:

```
|A| ≤ C(√y+(log m)(1+log y)),
∑_{p∤m}|b_p|² ≤ C y log y,
∑_{p∤m}|b_p| ≤ C y(1+log Z).
```

La prova della prima include tutte le potenze pari p^(2k) e i primi p|m. La prova dell'ℓ² delle `b_p` deve trattare attentamente le potenze dispari superiori: **non** è vero un limite costante `∑_{k≥3 dispari} c_y(p^k)≪log p min(1,y/p³)` se p³≪y, perché possono esserci ≫1 potenze prima di y. Separare p≤y^(1/3), con al più O(log y) per primo, e p>y^(1/3), con coda geometrica, per ottenere `O(y^(1/3)log² y)` nella somma dei quadrati degli errori.

Da `log m≤4 log U/(log Y)²≤4Y^(ε/5)` (usando anche il bound superiore di `admitted`) e `ε≤1`, `|A|² ≪ y log y` uniformemente per y≥Y.

## 6. Secondo momento: la candidata precisa di sostituzione

Per `T_q=∑_{p∤m}b_p(p/q)`, il modulo quadrato si espande; dato che il simbolo di Jacobi è reale,

```
∑_{q∈P}|T_q|² =
  |P| ∑_p|b_p|² +
  ∑_{p≠r} b_p ̅b_r ∑_{q∈P}(p/q)(r/q).
```

La somma totale è reale; usando triangolare e (CROSS) si ha:

```
[1/|P|]∑_{q∈P}|S_q|²
≤ 2|A|²+2∑_p|b_p|²+
  2 C'' U^(−13/192)(log U)² (∑_p|b_p|)².
```

Con `y≤Y^K`, `log Z=400 K log Y` e `log U≥Y^(ε/6)`, il terzo termine è
`O(U^(−13/192) (log U)² Y^(2K)(1+log Z)²)=o(1)` per ogni ε,K fissati, quindi assorbibile in `C y log y`.

**OBIETTIVO** (condizionale al Corollario 1.2, CRT e stime peso):

```
∃ C>0 assoluta, ∀ ε,K con 0<ε≤1 e K≥1, ∃ Y₀(ε,K),
∀ Y≥Y₀, ∀ U,m,a con admitted ε Y U m a,
∀ y∈[Y,Y^K], ∀ κ con |κ(n)|≤1:

∑_{q∈PPset(m,a,U)} |S(Y^(400K),y,q,κ)|²
   ≤ C y log y |PPset(m,a,U)|.
```

Questo coincide nella forma con `QH.meanSqK`, ma **non usa la sua ipotesi addizionale hp** sul fattore m e, se verificato, potrebbe evitare la dipendenza da `twistK` nel ramo B₂. È una sostituzione matematica nuova CANDIDATA, non un theorem Lean ottenuto. Non sappiamo ancora se esista un precedente nel paper del 21 novembre o nel lavoro complessivo di Alpöge.

## 7. Test finito eseguito, focalizzato sulla CRT (NON prova asintotica)

Python SymPy; U=100000, m=24, a=1; P=1176 primi q∈(√U,U] con q≡1 (mod24). In quattro coppie di primi distinti non divisori di m, confrontare la correlazione diretta `∑_{q∈P}(p/q)(r/q)` con `∑_{b∈R_{p,r}}σ(b)N_b` e verificare la cancellazione teorica `∑σ(b)=0`:

| p,r | #R=(p−1)(r−1) | ∑σ(b) | somma diretta | somma via residue |
|---|---:|---:|---:|---:|
| 5,7 | 24 | 0 | -22 | -22 |
| 5,11 | 40 | 0 | -6 | -6 |
| 7,13 | 72 | 0 | 12 | 12 |
| 11,17 | 160 | 0 | -18 | -18 |

Test esatto su interi, senza arrotondamenti dei simboli di Legendre/Jacobi. Verifica aritmetica del trasferimento in questi casi, non del corollario PNT-AP né del bound asintotico.

## 8. Gate scientifici obbligatori, e rischio di circolarità

- G0 **Fonte**: corollario OpenAI 11/12 presente nel paper originale, ma derivazione esterna dalla formula esplicita e importazione Lean da verificare.
- G1 **CRT/reciprocità**: dimostrare in Lean periodicità `(p/q)` mod 4p, cancellazione sui residui modulo mpr, e conteggio corretto delle classi con q≥√U.
- G2 **AP→correlazione**: formalizzare errore ≤#R E; questo è un lemma elementare condizionale e non prova G0-G1.
- G3 **PNT-AP→|P|**: dimostrare lower bound con esponenti, φ(m) e log U uniformi.
- G4 **Pesatura**: dimostrare stime `A,b_p` dal Chebyshev con tutte le potenze prime e quantificatori per κ arbitraria.
- G5 **Gram/MeanSq**: formalizzare la somma complessa dei quadrati, inserire G0-G4, compilare `MeanSq` in una copia Alpöge senza mutare l'originale.
- G6 **Originalità**: comparazione full text con tutte le semplificazioni 21 novembre; attribuire correttamente i risultati OpenAI, Alpöge e i classici.
- G7 **Onestà**: nessuna dichiarazione di risoluzione B₂, miglioramento GRH o prova RH prima di G0-G6.

### Riferimenti esatti

- [OpenAI 11/12, Corollary 1.2](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex)
- [QH.meanSqK Lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean)
- [QH.S, admitted, MeanSq Lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean)
- [Prior-art emerging discussion](https://hexagonmath.org/2611.00828v1)
