# Retained obsolete native artifacts

These four archives replace only the exact `artifacts` directories named in their manifests. Source, logs, results, current `.lake` outputs and other work remain at their original locations. Each archive was streamed through an independent SHA-256 and metadata comparison before its original directory was retired; each original was hashed again immediately before retirement.

For one label (`context-batch-01`, `value-visibility-01`, `value-visibility-02`, or `binding-application-phases-01`):

1. Compare the archive and manifest SHA-256 with that label's `archive-verification.json` and `retirement.json`.
2. Ensure the original target directory is absent and there is enough free space for the manifest's full allocated size. Never extract over an existing candidate.
3. From the repository root, run GNU tar with the exact archive path:

```sh
tar --zstd --extract --file timing/logs/20261126-obsolete-artifact-retention-01/LABEL.tar.zst --same-owner --same-permissions --acls --xattrs --xattrs-include='*' --selinux
```

4. Recompute every regular-file SHA-256 and compare file/directory modes, numeric owners and nanosecond modification times with `LABEL.manifest.json`. The archive verification records contain the complete comparison and original paths.
5. Restore each entry's recorded `atime_ns` and `mtime_ns` with `os.utime(path, ns=(atime_ns, mtime_ns), follow_symlinks=False)`, applying directory timestamps last. The original kernel inode/device/change-time/link/block metadata is preserved in the manifest; kernel-assigned identities and ctime cannot be recreated by extraction.

The PAX archives also retain extended metadata. No original entry had extended attributes, symbolic links or multiply linked regular files. The protected baseline and final verification record document unchanged source/log/result files and the live `.lake` tree. No native validation was run during this storage recovery.
