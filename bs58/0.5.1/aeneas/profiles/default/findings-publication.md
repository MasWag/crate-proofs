# Findings publication companion

`proofs.toml` is consumed by the pinned managed cargo-proofs CLI, which does not parse `[[report.findings]]`. Its four proof mappings remain in that report. The three independently reproduced checksum findings are in `findings.json` with stable idempotency keys and their affected API paths. This separation is a CLI compatibility boundary, not a formal verification result.

After the proof report has a published report ID, create each finding through the documented `POST /api/v1/reports/{report_id}/findings` endpoint. For each entry, send only its `title` and `body` as JSON; use `idempotency_key` as the `Idempotency-Key` request header. The `api_paths` field is an editorial inventory and is already named in each body; it is not sent as an unverified API ID. Reuse the same key and body for retries, and retain the returned finding IDs in publication evidence. The endpoint requires a publish token or a valid logged-in session.

The API reference is `book/src/api-documentation.md` in the pinned proofs-rs source and the live site at `/api/docs`. Posting findings is an external write and must be checked separately from local Lean verification. A successful `cargo proofs run` does not create these three findings.
