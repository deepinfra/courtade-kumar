import Reveal from "../reveal/index";
import { renderElement } from "../latex/latex";
import { getSvgElem, SvgElem, SvgMatrix, SvgText } from "../svg/SvgElem";

const drawDiagram = (id: string, reveal: boolean): void => {
  const x = "100110101101110";
  const y = "101110100101100";
  const z = [...x].map((bit, i) => bit === y[i] ? "0" : "1").join("");
  const palette = { "1": "#fee", s: "#ddd" };

  const svg = getSvgElem(id)
    .add(new SvgMatrix(80, 30, 40, 40, [x], [z], palette, reveal ? 0 : undefined))
    .add(new SvgText(14, 61, "X"))
    .add(new SvgText(44, 64, "="));

  const cBoxY = 260;
  const cFragment = new SvgElem("g")
    .add(new SvgElem("polygon").withAttributes({
      points: "84,170 380,270 676,170",
      fill: "#28a0eb",
      "fill-opacity": 0.28,
      stroke: "none",
    }))
    .add(new SvgElem("path").withAttributes({
      d: "M84 170L380 270L676 170",
      fill: "none",
      stroke: "#48aeef",
      "stroke-width": 2.5,
    }))
    .add(new SvgElem("path").withAttributes({
      d: "M84 170H676",
      fill: "none",
      stroke: palette.s,
      "stroke-width": 2,
    }))
    .add(new SvgElem("rect").withAttributes({
      x: 360, y: cBoxY, width: 40, height: 40,
      rx: 4, ry: 4,
      fill: "white",
      stroke: palette.s,
      "stroke-width": 2,
    }))
    .add(new SvgText(380, cBoxY + 31, "C")
      .withAttributes({ "text-anchor": "middle" }));

  const yRow = new SvgElem("g")
    .add(new SvgElem("rect").withAttributes({
      x: 80, y: 130, width: 600, height: 40, fill: "white",
    }))
    .add(new SvgMatrix(80, 130, 40, 40, [y], [z], palette))
    .add(new SvgText(14, 161, "Y"))
    .add(new SvgText(44, 164, "="));

  // Keep the triangle behind Y, whose lower border hides its base.
  if (reveal)
    svg.addFrag(cFragment, 1).addFrag(yRow, 0);
  else
    svg.add(cFragment).add(yRow);
};

const drawInductionStepDiagram = (
  id: string, includeComparisonBit = false,
): void => {
  const cell = 38;
  const left = 130;
  const xTop = 4;
  const yTop = 68;
  const cTop = 148;
  const rowWidth = cell * 10;
  const mergeStart = 2;
  const mergeEnd = 7;
  const palette = {
    blue: "#28a0eb",
    blueOutline: "#48aeef",
    purple: "#8c52eb",
    purpleOutline: "#9d6cee",
    pink: "#f252a0",
    pinkOutline: "#f46eb1",
    grid: "#999",
    innerGrid: "#b3b3b3",
    arrow: "#595959",
  };
  const svg = getSvgElem(id);
  const arrowId = `${id}-arrow`;

  const makeRow = (
    y: number, selectedColor: string, selectedOutline: string,
    rowLabel: string, selectedLabel: string,
  ): SvgElem => {
    const selectedX = left + 9 * cell;
    const row = new SvgElem("g")
      .add(new SvgElem("rect").withAttributes({
        x: left, y, width: rowWidth, height: cell, fill: "white",
      }))
      .add(new SvgElem("rect").withAttributes({
        x: selectedX, y, width: cell, height: cell,
        fill: selectedColor, "fill-opacity": 0.28,
      }));

    for (let slot = 1; slot < 10; slot++) {
      if (slot > mergeStart && slot < mergeEnd)
        continue;
      row.add(new SvgElem("path").withAttributes({
        d: `M${left + slot * cell} ${y + 1}v${cell - 2}`,
        stroke: palette.innerGrid, "stroke-width": 1.2,
      }));
    }

    row.add(new SvgElem("rect").withAttributes({
      x: left, y, width: rowWidth, height: cell,
      fill: "none", stroke: palette.grid, "stroke-width": 1.5,
    }))
      .add(new SvgElem("rect").withAttributes({
        x: selectedX, y, width: cell, height: cell,
        fill: "none", stroke: selectedOutline, "stroke-width": 2.5,
      }))
      .add(new SvgText(left + 9.5 * cell, y + cell / 2, selectedLabel).withAttributes({
        "text-anchor": "middle",
        "dominant-baseline": "central",
      }))
      .add(new SvgText(40, y + 25, rowLabel))
      .add(new SvgText(82, y + 26, "="));
    return row;
  };

  const arrowMarker = new SvgElem("marker").withAttributes({
    id: arrowId,
    viewBox: "0 0 9 9",
    refX: 9,
    refY: 4.5,
    markerWidth: 9,
    markerHeight: 9,
    markerUnits: "userSpaceOnUse",
    orient: "auto",
  }).add(new SvgElem("path").withAttributes({
    d: "M0 0L9 4.5L0 9Z",
    fill: palette.arrow,
  }));

  const mergedCenter = left + ((mergeStart + mergeEnd) / 2) * cell;
  const selectedCenter = left + 9.5 * cell;
  const arrows = new SvgElem("g")
    .add(new SvgElem("path").withAttributes({
      d: `M${left + 9 * cell + 5} ${cTop} C${left + 8 * cell} 130 ${mergedCenter + 100} 116 ${mergedCenter} ${yTop + cell}`,
      fill: "none",
      stroke: palette.arrow,
      "stroke-width": 1.6,
      "stroke-linecap": "round",
      "marker-end": `url(#${arrowId})`,
    }))
    .add(new SvgElem("path").withAttributes({
      d: `M${selectedCenter} ${cTop}V${yTop + cell}`,
      fill: "none",
      stroke: palette.arrow,
      "stroke-width": 1.6,
      "marker-end": `url(#${arrowId})`,
    }));

  const cPrimeX = left + 10 * cell + 10;
  const cPrimeArrow = new SvgElem("path").withAttributes({
    d: `M${cPrimeX + 5} ${cTop} C${cPrimeX - 5} 130 ${cPrimeX - 14} 116 ${left + 10 * cell - 7} ${yTop + cell}`,
    fill: "none",
    stroke: palette.arrow,
    "stroke-width": 1.6,
    "stroke-linecap": "round",
    "marker-end": `url(#${arrowId})`,
  });

  const cBox = new SvgElem("g")
    .add(new SvgElem("rect").withAttributes({
      x: left + 9 * cell, y: cTop, width: cell, height: cell,
      fill: palette.pink, "fill-opacity": 0.12,
      stroke: palette.pinkOutline, "stroke-width": 2.5,
    }))
    .add(new SvgText(selectedCenter, cTop + cell / 2, "C").withAttributes({
      "text-anchor": "middle",
      "dominant-baseline": "central",
    }));

  const cPrimeBox = new SvgElem("g")
    .add(new SvgElem("rect").withAttributes({
      x: cPrimeX, y: cTop, width: cell, height: cell,
      fill: "#e5a900", "fill-opacity": 0.12,
      stroke: "#e9b926", "stroke-width": 2.5,
    }))
    .add(new SvgText(cPrimeX + cell / 2, cTop + cell / 2, "C′").withAttributes({
      "text-anchor": "middle",
      "dominant-baseline": "central",
    }));

  svg.add(new SvgElem("defs").add(arrowMarker))
    .add(makeRow(xTop, palette.purple, palette.purpleOutline, "X", "A"))
    .add(makeRow(yTop, palette.blue, palette.blueOutline, "Y", "B"))
    .add(arrows)
    .add(cBox);

  if (includeComparisonBit)
    svg.add(cPrimeArrow).add(cPrimeBox);
};

drawDiagram("svg-defn", true);
drawDiagram("svg-courtade-kumar", false);
drawInductionStepDiagram("svg-induction-step");
drawInductionStepDiagram("svg-remaining-terms", true);

for (const element of document.querySelectorAll(".texnify"))
  renderElement(element);

export const startPresentation = async (): Promise<void> => {
  const presentation = new Reveal({
    width: 1200,
    height: 675,
    margin: 0,
    minScale: 0.1,
    maxScale: 8,
    center: false,
    controls: false,
    progress: false,
    slideNumber: true,
    hash: true,
    transition: "slide",
    scrollActivationWidth: 0,
  });
  await presentation.initialize();
  await document.fonts.ready;
  presentation.layout();
};

await startPresentation();
