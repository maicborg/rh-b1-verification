# RH-B1: ponte OpenAI 7/8 → Alpöge

**Responsabile del programma e della direzione concettuale:** Maicol Borghetti  
**Laboratorio:** Teoria dello Zero, progetto RH  
**Preparazione del codice:** GPT-6, sotto direzione del laboratorio  
**Data:** 22 novembre 2026  
**Stato:** **PONTE CONDIZIONALE VERIFICATO IN LEAN (22/11/2026); collegamento con il vero teorema OpenAI NON ancora certificato.**

**Evidenza:** [GitHub Actions — compilazione riuscita, run 45070169275](https://github.com/maicborg/rh-b1-verification/actions/runs/45070169275). Lean 4.34.1, Mathlib alla revisione `d13f23b7...`; `#print axioms BorghettiRH.badB1_empty`: `[propext, Classical.choice, Quot.sound]`. La dimostrazione richiede l'ipotesi esplicita `h78`, parte del suo enunciato.

## Risultato che vogliamo certificare

Nel file originale `StagePow.lean`, la prova `QH.stage` separa i moduli cattivi in `B₁` e `B₂`. Il ramo `B₁` contiene soltanto moduli primi `q ≥ 2` e caratteri **primitivi** di livello `f*q` che violano `ZeroFreeBox`.

Il teorema OpenAI fornisce `L(s,χ) ≠ 0` per `Re(s)>7/8`, tranne il caso `χ=1, s=1`. Poiché un carattere primitivo principale ha conduttore 1, questo caso è escluso quando il livello è divisibile da `q ≥ 2`.

`ZeroFreeBox` richiede soltanto `Re(s) > 399/400`; dunque **`B₁ = ∅`** segue dalla combinazione dei teoremi già dimostrati. La definizione `BadB1` del test è un **sovrainsieme** del `B₁` originale: omette alcuni vincoli aggiuntivi su `F, U`; dimostrarlo vuoto basta per il ramo originale. **Non significa che l'intera dimostrazione RH sia stata accorciata o ricompilata.**

## File

| File | Che cosa verifica | Stato |
|---|---|---|
| `B1Standalone.lean` | Implicazione `h78 → BadB1=∅` in Mathlib. **h78 è un'ipotesi esplicita.** | **Compilato e verificato**; `h78` rimane un'ipotesi dell'enunciato |
| `B1OpenAI.lean` | Usa **il teorema OpenAI importato**, senza ipotesi `h78` aggiunta. | Non compilato; necessita del pesante progetto OpenAI |
| `.github/workflows/lean-b1-direct.yml` | Avvia automaticamente Lean, `lake update`, cache Mathlib, test razionale e ponte condizionale. | **Riuscito**, run `45070169275` |
| `.github/workflows/lean-bridge.yml` | Verifica manuale alternativa del ponte condizionale. | Disponibile |
| `.github/workflows/lean-openai-bridge.yml` | Copia il sorgente dal repository OpenAI al commit `4eaee875...` in un ambiente isolato e tenta l'import reale. | Verifica sperimentale distinta |
| `B1RationalGap.lean` | Verifica il confronto razionale fra le soglie. | **Compilato** |
| `CITATION.cff`, `AUTHORS.md` | Metadati attribuiti a Maicol Borghetti e riconoscimento fonti/IA. | Preparati |

## Primo controllo: solo ponte condizionale

1. Il repository è pubblicato e GitHub Actions ha già verificato con successo `B1Standalone.lean`: [run 45070169275](https://github.com/maicborg/rh-b1-verification/actions/runs/45070169275).
2. Verde certifica **soltanto** che Lean ha accettato l'implicazione condizionale: l'ipotesi `h78` non è stata ancora collegata al teorema importato.
3. Per riprodurre localmente il controllo: `lake update`, `lake exe cache get`, `lake env lean B1RationalGap.lean` e `lake env lean B1Standalone.lean`; leggere la riga `#print axioms BorghettiRH.badB1_empty`.
4. Le vecchie Actions rosse si sono fermate per problemi di setup/import; non costituiscono controesempi alla dimostrazione.

## Secondo controllo: teorema OpenAI effettivamente importato

1. Preparare **una copia di lavoro separata** del repository https://github.com/openai/math nella sua sottocartella `lean/` (toolchain 4.34.1). La compilazione è pesante, richiede le dipendenze del repository e può non funzionare su normali runner gratuiti.
2. Copiare **solo** `B1OpenAI.lean` nella root `lean/` di quella copia: non modificare le definizioni originali OpenAI.
3. Dopo aver costruito/recuperato le dipendenze richieste dal progetto, eseguire dalla stessa root: `lake env lean B1OpenAI.lean`. Leggere gli errori (se presenti); non ignorarli.
4. Richiedere assenza di `sorry`, `admit` e assunzioni extra e leggere `#print axioms` del teorema finale. Salvare output, SHA di commit, toolchain e identificativo della CI.

Se il secondo controllo riesce, abbiamo certificato il **lemma locale in un ambiente coerente con il teorema OpenAI**. Resterebbe da verificare l'integrazione nel Lean Alpöge (toolchain 4.33.1), il risparmio effettivo di `count_bad`, la prova di `B₂` e l'originalità bibliografica.

## Riferimenti di audit

- OpenAI: https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean — blob `46c67f4000906b1391a471d6e6396ac0da3c16a5` alla lettura.
- Alpöge (mirror, **commit fisso** `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`):
  - `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean` — blob `2f7159075ea0e309f4a7ff7e237ede7b71bbe5e7`.
  - `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean` — blob `bdea967f4db26bfc2b040f01beeebbed0ff8909c`.
- Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletCharacter/Basic.html
- Relazione scientifica lab RH: `DOC-20261122-38342fc2ce`, `DOC-20261122-0ce230263a`, `DOC-20261122-da87a08f48`.

## Originalità e riconoscimento

È un controllo incrociato di risultati pubblicati, non una prova originale di RH. Per costruire un contributo pubblicabile occorre **una semplificazione realmente integrata, rigorosa, riproducibile e distinta da lavori precedenti**. Il nome nel repository, gli autori in `CITATION.cff`, i commit e un'eventuale versione archiviata (Zenodo DOI dopo validazione) ne documentano la provenienza, non certificano la novità.
