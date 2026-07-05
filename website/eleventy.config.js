module.exports = function (eleventyConfig) {
  eleventyConfig.addPassthroughCopy("src/assets");
  eleventyConfig.addPassthroughCopy("src/robots.txt");
  eleventyConfig.addPassthroughCopy("src/CNAME");
  eleventyConfig.addPassthroughCopy("src/.nojekyll");

  // Relative prefix from a page URL back to the site root ("./", "../", ...).
  eleventyConfig.addFilter("relprefix", (url) => {
    const depth = url.split("/").length - 2;
    return depth <= 0 ? "./" : "../".repeat(depth);
  });

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
