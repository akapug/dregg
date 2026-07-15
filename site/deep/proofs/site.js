(() => {
  const header = document.querySelector("[data-header]");
  const axisButtons = [...document.querySelectorAll("[data-axis]")];
  const substrateEntries = [...document.querySelectorAll("[data-axes]")];
  const emptyState = document.querySelector("[data-filter-empty]");

  const updateHeader = () => {
    header?.classList.toggle("is-scrolled", window.scrollY > 24);
  };

  const selectAxis = (axis) => {
    let visible = 0;

    axisButtons.forEach((button) => {
      const selected = button.dataset.axis === axis;
      button.classList.toggle("is-active", selected);
      button.setAttribute("aria-pressed", String(selected));
    });

    substrateEntries.forEach((entry) => {
      const axes = entry.dataset.axes?.split(" ") ?? [];
      const show = axis === "all" || axes.includes(axis);
      entry.hidden = !show;
      visible += show ? 1 : 0;
    });

    if (emptyState) {
      emptyState.hidden = visible !== 0;
    }
  };

  axisButtons.forEach((button) => {
    button.addEventListener("click", () => selectAxis(button.dataset.axis ?? "all"));
  });

  updateHeader();
  window.addEventListener("scroll", updateHeader, { passive: true });
})();
