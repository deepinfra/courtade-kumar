# Courtade–Kumar slides

From this directory:

```sh
bun install
bun run start
```

This builds once and serves the deck at <http://127.0.0.1:8001/>. Use the arrow
keys to navigate. `SLIDES_PORT=8080 bun run start` selects another port.

```sh
bun run build   # Build only
bun run serve   # Serve the existing build
bun run check   # Type-check
bun test        # Check the build and serving contracts
```

The Makefile provides `make local_deploy`, `make run`, and
`make runnocompile`, matching the homepage's build-then-serve workflow.
There is no file watcher or HMR; rebuild and refresh after editing.

## Source

- `entry/entry.html` contains every slide declaration and the page metadata.
- `entry/entry.ts` is the browser entry point, using ES module imports.
- `entry/entry.css` collects shared and component styles.
- `title/` contains the title slide styles.
- `reveal/` configures navigation and the 1200 × 675 coordinate system.
- `latex/` is a local copy of the homepage renderer and stylesheet. The build
  renders `$…$` and `$$…$$` in the HTML; no math renderer runs in the browser.
- `gito/` declares the original Hamming fonts from the local `font/` directory,
  using weight 300 for the title and authors. These font files remain untracked.
- `tools/` contains the independent Bun build and static server.

This is a folder convention, with no component framework or TSX runtime.
Reveal.js is imported from npm; the old Hamming deck lives in the heatdiscrete
paper repository.

## Output

`build/bundle/` contains `index.html`, flat content-hashed JavaScript, CSS, and
fonts, plus gzip/Brotli variants of HTML, JavaScript, and CSS. Asset hashes use
the same eight-character format and algorithm as the homepage, computed after
rewriting the font URLs.

All asset references start with `/`, including fonts referenced by CSS. A host
may mount the HTML at any route, provided it serves these hashed assets at the
origin root. Homepage collection and Cloudflare deployment are deliberately
outside this package.

For a combined local preview, run these from the homepage repository:

```sh
bun papers/courtade-kumar/slides/tools/build.ts
bun run start
```

The homepage's `[slides]` link opens `/talks/courtade-kumar`. Its server reads
the deck directly from this package's `build/bundle/` and finds root-level
hashed assets across the homepage and paper bundles. Rebuild a deck and refresh
to see changes; the server does not copy or merge bundles. With existing builds,
`bun tools/server.ts` is enough.

Paths are resolved relative to the package, so running
`bun /absolute/path/to/slides/tools/build.ts` also works from another directory.
