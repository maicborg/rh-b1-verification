> **Aggiornamento V2 (22/11/2026):** [B2-AP11-12-DIRECT-REPLACEMENT.md](B2-AP11-12-DIRECT-REPLACEMENT.md) mostra una via più diretta: il **Corollario 1.2 già enunciato** nel manoscritto OpenAI 11/12 sulle progressioni aritmetiche, CRT e reciprocità quadratica conducono a un possibile rimpiazzo della stima `meanSqK`. [B2APTransfer.lean](B2APTransfer.lean) formalizza passaggi combinatori *condizionali* della conversione; il Corollario quantitativo OpenAI e la dimostrazione finale per `S` NON sono ancora importati in Lean. I dettagli e i falsificatori sono nella nota V2. La nota QRH78 V1 rimane consultabile come ipotesi precedente.

> **Nuova linea analitica del 22/11/2026 — non ancora Lean verificata:** [B2-Q78-QUADRATIC-CORRELATION-RESEARCH.md](B2-Q78-QUADRATIC-CORRELATION-RESEARCH.md). Propone di ricavare da QRH(7/8) una stima uniforme dei primi in progressioni, sostituendo nel mean square di B₂ l'analisi dell'eccezione nstar e il passaggio twistK con correlazioni quadratiche di simboli di Jacobi. Documento di ricerca con ipotesi, bounds, falsificatori e un test numerico dell'identità. Il solo `B2Budget.lean` è kernel verificato; il nuovo rimpiazzo analitico NON lo è.

# B₂ — stato della ricerca (22 novembre 2026)

Direzione di ricerca: Maicol Borghetti (@maicborg), laboratorio RH Teoria dello Zero.
Formalizzazione e audit assistiti da GPT-6.

## Quello che esiste già nella prova Alpöge
Levent Alpöge fornisce una dimostrazione Lean del controllo di B₂:
- `meanSqK` controlla la **media dei quadrati** della somma aritmetica `S Z y q κ` sui primi q del `PPset`, uniformemente sulle finestre di y.
- `bad_share` trasforma questa stima in una stima della **cardinalità** dei primi q che violano una soglia sulla somma `S`, anche quando il punto y varia con q.
- `QH.stage` usa queste stime dopo aver separato `B₁` e `B₂`.

Questi risultati sono risultati **preesistenti**, non nostri.

Sorgenti fissate al commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`:
- [StagePow.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean), righe 100–170.
- [meanSqK.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean), teorema alle righe 50–54.
- [BadShare.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean), teorema `bad_share` alle righe 251–254.

## Prova B₂ attuale del nostro repository
Il file [B2Budget.lean](./B2Budget.lean) ha **compilato correttamente in Lean 4.34.1**: [GitHub Actions run 45072303363](https://github.com/maicborg/rh-b1-verification/actions/runs/45072303363). Verifica un **lemma combinatorio condizionale**:
se B₁ è vuoto, B è coperto dall'unione di B₂(ξ), |Ξ|≤R e, per ogni ξ,
`|B₂(ξ)| ≤ η/(R+1) · |P|`, allora `|B| ≤ η |P|`.

La stima `|B₂(ξ)| ≤ η/(R+1) |P|` è **IPOTESI ESPLICITA del lemma** e non è dimostrata da questo file. Il suo significato è soltanto che il budget individuale per B₂ può essere raddoppiato rispetto a quello usato in `StagePow.lean`, che è `η/[2(R+1)]`. Il vecchio limite può essere ottenuto dalla dimostrazione originale di `bad_share` scegliendo un diverso parametro, ma questo non elimina né migliora l'ingrediente analitico.

## Cosa servirebbe per una nuova semplificazione sostanziale
1. Identificare un teorema più corto o più debole che fornisca la stessa stima uniforme sui primi q e sulle finestre di y, oppure che permetta di evitare `meanSqK` o la procedura dyadica in `bad_share`.
2. Dimostrare senza usare RH e con quantificatori comparabili le ipotesi analitiche di quel sostituto.
3. Integrare il nuovo lemma nel proof term Alpöge `QH.stage` (toolchain originale 4.33.1), senza `sorry`, e verificare quali dipendenze e soglie siano effettivamente eliminate.
4. Confrontare ogni novità con la letteratura più recente, incluse le semplificazioni terze pubblicate il 21 novembre 2026.

**Situazione: B₁ condizionale verificato da Lean; B₂ conteggio condizionale verificato da Lean, assiomi [propext, Classical.choice, Quot.sound]; nessuna nuova prova analitica di B₂ e nessuna nuova dimostrazione RH.**
