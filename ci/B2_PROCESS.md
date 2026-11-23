# B₂ — Procedura GitHub riproducibile (23 novembre 2026)

**Branch di ricerca:** `b2/incremental-ci`. **Pipeline unica:** `.github/workflows/b2-incremental.yml`. **Patch versionate:** `ci/b2_prepare.py`.

## Obiettivo
Portare nel medesimo kernel Lean 4.34.1 i sorgenti fissati OpenAI (`4eaee87548250b2682affda7d05d947c05554bae`) e Alpöge (`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`) per testare una sostituzione senza parametro esterno `h78` della catena B₂. I repository originali **non vengono modificati**: ogni tentativo usa checkout separati ed effimeri GitHub Actions.

## Gates (NON confonderli)
0. **Preflight Python** — controlla presenza dei bridge e compatibilità degli schemi delle patch contro i sorgenti esatti. Non installa Lean. Qualsiasi errore di indentazione o sequenza inattesa ferma il job in anticipo.
1. **Compatibilità** — compila solo i moduli modificati dalla migrazione delle API Mathlib, per isolare gli errori prima del target finale.
2. **PNTFinal originale Alpöge** — il lemma deve compilare nel medesimo progetto Lean dell'OpenAI autentico.
3. **Bridge effettivo OpenAI 7/8 + PNT** — non basta una variabile `h78`: serve un termine di prova reale importato e compilato.
4. **twistK, meanSqK, StagePow** — stesso kernel e dichiarazioni finali corrispondenti alle firme originali, senza assunzioni aggiunte.
5. **Audit** — `#print axioms`, assenza di `sorryAx`, analisi assiomi e dipendenze transitive, indipendenza dei risultati dai lemmi bersaglio.

**Solo il completamento di tutti i gates e l'audit delle dipendenze consentono di discutere B₂ come chiuso.** Una compilation verde di un lemma condizionale non è sufficiente.

## Uso
Ogni push al branch che modifica il file del workflow, `ci/b2_prepare.py` o i bridge `B2*.lean` avvia la pipeline. `workflow_dispatch` consente anche di limitarsi a `preflight`, `compat` o `pnt`; `full` percorre tutti i gates. Sono sempre salvati gli artifact `b2-preflight-<run-id>` e, se avviato, `b2-build-<run-id>`; anche in caso di fallimento. I log si leggono prima di qualunque modifica.

Una nuova correzione deve seguire: **ultima run → primo step fallito → primo errore primario → verifica sorgente → patch minima nello stesso file → push sul medesimo branch**. Non creare altri YAML denominati v7, v8, ecc. Non rilanciare invariato un errore deterministico. Non fare force-push.

## Limiti
Il branch e le cache GitHub sono persistenti; **i runner delle Actions non lo sono**. Nessuna azione GitHub corregge autonomamente un errore di compilazione: l'automazione RH0 verifica l'esito alla successiva esecuzione programmata, interviene sul branch autorizzato ove possibile e scrive il suo resoconto append-only nel laboratorio. Se la sessione non può correggere, segnala il blocco preciso. I workflow storici su main restano soltanto documentazione delle prove tentate.

Responsabile progetto: Maicol Borghetti. Codice e audit: GPT-6. Nessuna rivendicazione di dimostrazione RH/GRH.
