const menuButton = document.querySelector('[data-menu]');
const sideNav = document.querySelector('.side-nav');
if (menuButton && sideNav) {
  menuButton.addEventListener('click', () => {
    const open = sideNav.classList.toggle('open');
    menuButton.setAttribute('aria-expanded', String(open));
  });
}

const searchDialog = document.querySelector('#search-dialog');
const searchInput = document.querySelector('#search-input');
const searchResults = document.querySelector('#search-results');
let searchIndex;

async function openSearch() {
  if (!searchDialog) return;
  searchDialog.showModal();
  searchInput.focus();
  if (!searchIndex) searchIndex = await fetch('assets/search-index.json').then(r => r.json());
}

document.querySelectorAll('[data-search]').forEach(button => button.addEventListener('click', event => {
  event.preventDefault();
  openSearch();
}));

document.addEventListener('keydown', event => {
  if ((event.metaKey || event.ctrlKey) && event.key.toLowerCase() === 'k') {
    event.preventDefault();
    openSearch();
  }
});

if (searchInput) {
  searchInput.addEventListener('input', () => {
    const query = searchInput.value.trim().toLowerCase();
    if (!query || !searchIndex) {
      searchResults.innerHTML = '<p>Search topics and task IDs across the handbook.</p>';
      return;
    }
    const terms = query.split(/\s+/);
    const matches = searchIndex.filter(item => terms.every(term => item.text.includes(term))).slice(0, 12);
    searchResults.innerHTML = matches.length ? matches.map(item =>
      `<a class="search-result" href="${item.url}"><strong>${item.title}</strong><span>${item.section}</span></a>`
    ).join('') : '<p>No matching section found.</p>';
  });
}

if (searchDialog) {
  searchDialog.addEventListener('click', event => {
    if (event.target === searchDialog) searchDialog.close();
  });
}

if (window.renderMathInElement) {
  renderMathInElement(document.body, {
    delimiters: [
      {left: '$$', right: '$$', display: true},
      {left: '$', right: '$', display: false}
    ],
    throwOnError: false
  });
}
