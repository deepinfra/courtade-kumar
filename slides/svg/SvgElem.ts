/** SVG drawing primitives from the Hamming slides, converted to TypeScript. */
export class SvgElem {
  readonly elem: SVGElement;

  constructor(arg: string | SVGElement) {
    this.elem = typeof arg === "string"
      ? document.createElementNS("http://www.w3.org/2000/svg", arg)
      : arg;
  }

  withAttributes(attrs: Record<string, string | number>): this {
    for (const attr in attrs)
      this.elem.setAttribute(attr, String(attrs[attr]));
    return this;
  }

  add(child: SvgElem): this {
    this.elem.appendChild(child.elem);
    return this;
  }

  addFrag(child: SvgElem, index: number): this {
    child.withAttributes({ "data-fragment-index": index });
    child.elem.classList.add("fragment");
    return this.add(child);
  }
}

export const getSvgElem = (id: string): SvgElem =>
  new SvgElem(document.querySelector<SVGElement>(`#${id}`)!);

export class SvgText extends SvgElem {
  constructor(x: number, y: number, content: string, color?: string) {
    super("text");
    this.withAttributes({ x, y });
    if (color)
      this.withAttributes({ fill: color });
    this.elem.textContent = content;
  }
}

const createGrid = (
  x: number, y: number, cellWidth: number, cellHeight: number,
  cols: number, rows: number, palette: Record<string, string>,
): SvgElem => {
  const width = cellWidth * cols;
  const height = cellHeight * rows;
  const grid = new SvgElem("g").add(new SvgElem("rect").withAttributes({
    x, y, width, height, rx: 4, ry: 4,
    stroke: palette.s, fill: "none", "stroke-width": 2,
  }));

  for (let col = 1; col < cols; col++)
    grid.add(new SvgElem("path").withAttributes({
      d: `M${x + col * cellWidth} ${y + 1}v${height - 2}`,
      stroke: palette.s, "stroke-width": 2,
    }));
  for (let row = 1; row < rows; row++)
    grid.add(new SvgElem("path").withAttributes({
      d: `M${x + 1} ${y + row * cellHeight}h${width - 2}`,
      stroke: palette.s, "stroke-width": 2,
    }));
  return grid;
};

export class SvgMatrix extends SvgElem {
  /** colorFragmentIndex optionally reveals the colored cells as one fragment step. */
  constructor(
    x: number, y: number, cellWidth: number, cellHeight: number,
    content: readonly (string | readonly string[])[],
    colors: readonly (string | readonly string[])[],
    palette: Record<string, string>,
    colorFragmentIndex?: number,
  ) {
    const rows = content.length;
    const cols = content[0].length;
    super(createGrid(x, y, cellWidth, cellHeight, cols, rows, palette).elem);

    for (let row = 0; row < rows; row++) {
      for (let col = 0; col < cols; col++) {
        const cx = x + col * cellWidth;
        const cy = y + row * cellHeight;
        const color = colors[row][col];
        if (color !== "0") {
          const fill = new SvgElem("rect").withAttributes({
            x: cx + 1, y: cy + 1,
            width: cellWidth - 2, height: cellHeight - 2,
            fill: palette[color],
          });
          if (colorFragmentIndex === undefined)
            this.add(fill);
          else
            this.addFrag(fill, colorFragmentIndex);
        }
        this.add(new SvgText(
          cx + cellWidth / 2 - 8, cy + cellHeight / 2 + 11,
          content[row][col], palette.text,
        ));
      }
    }
  }
}
