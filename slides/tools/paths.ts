import { resolve } from "node:path";

export const SlidesRoot = resolve(import.meta.dir, "..");
export const BundleRoot = resolve(SlidesRoot, "build/bundle");
