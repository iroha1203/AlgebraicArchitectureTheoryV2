module.exports = function (eleventyConfig) {
  eleventyConfig.addPassthroughCopy("src/assets");
  eleventyConfig.addPassthroughCopy("src/robots.txt");
  eleventyConfig.addPassthroughCopy("src/CNAME");
  eleventyConfig.addPassthroughCopy("src/.nojekyll");
  eleventyConfig.addPassthroughCopy("src/_redirects");
  eleventyConfig.addPassthroughCopy("src/favicon.ico");

  // ArchView public demo: publish the tooling source of truth without a
  // second checked-in copy under website/src.
  eleventyConfig.addPassthroughCopy({ "../tools/archview/archview.html": "archsig/archview/viewer/archview.html" });
  eleventyConfig.addPassthroughCopy({ "../tools/archview/archview-assets": "archsig/archview/viewer/archview-assets" });

  // Relative prefix from a page URL back to the site root ("./", "../", ...).
  eleventyConfig.addFilter("relprefix", (url) => {
    const depth = url.split("/").length - 2;
    return depth <= 0 ? "./" : "../".repeat(depth);
  });

  // Pages of one nav section in reading order, shaped for the series-nav panel.
  eleventyConfig.addFilter("sectionSeries", (pages, section) =>
    pages
      .filter((p) => p.data.navSection === section)
      .map((p) => ({
        path: p.url.slice(1),
        title: p.data.title,
        depth: p.url.split("/").filter(Boolean).length,
      }))
  );

  // All public pages in curated reading order (front matter `order`).
  eleventyConfig.addCollection("pages", (api) =>
    api
      .getFilteredByGlob("src/**/index.html")
      .sort((a, b) => a.data.order - b.data.order)
  );

  return {
    dir: {
      input: "src",
      output: "_site",
      layouts: "_layouts",
      includes: "_includes",
      data: "_data",
    },
    htmlTemplateEngine: "njk",
    markdownTemplateEngine: "njk",
  };
};
