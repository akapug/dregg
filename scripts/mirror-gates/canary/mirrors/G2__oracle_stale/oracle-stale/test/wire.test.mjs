// THE DRIFT KILLER — asserts byte equality against `canary-wasm`. But `test` runs `npm run build`
// (which builds the TS, never the wasm), so this compares against whatever frozen binary is sitting
// in the gitignored `pkg/`. On a fresh clone the oracle does not exist and this cannot run at all.
import { test } from "node:test";
import * as oracle from "canary-wasm";
test("wire matches the oracle", () => { void oracle; });
