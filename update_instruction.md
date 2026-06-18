# Update instructions (before every push)

- Update `roadmap.md` and `README.md` by hand (status, sorry counts, papers).
- Regenerate scope DAG (if members/deps changed): `archon scope roadmap`
- Build the static dashboard: `archon scope dashboard --static-build`
- Commit **and push** everything incl. `docs/` — Pages only deploys what's pushed to `main`:
  ```bash
  git add roadmap.md README.md .archon-scope/ docs/
  git commit -m "Update roadmap + rebuild dashboard"
  git push origin main
  ```
