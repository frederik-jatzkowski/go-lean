"""Stage repository Markdown as MkDocs pages and resolve links to source files."""

from pathlib import Path
from urllib.parse import quote, unquote, urlsplit, urlunsplit

from markdown.extensions import Extension
from markdown.treeprocessors import Treeprocessor
from mkdocs.structure.files import File
from pygments.formatters import HtmlFormatter


ROOT_PAGES = ("README.md", "CONTRIBUTING.md")


def on_config(config):
    config.markdown_extensions.append(RepositoryLinks())
    return config


def on_files(files, config):
    root = Path(config.config_file_path).resolve().parent
    sources = [root / name for name in ROOT_PAGES]
    sources.extend(sorted(root.glob("examples/proven/*/README.md")))
    for file in list(files):
        if file.src_dir == config.docs_dir:
            files.remove(file)
            if file.is_documentation_page() or (
                file.is_media_file() and file.src_uri.startswith("images/")
            ):
                sources.append(Path(file.abs_src_path))
    for source in sources:
        files.append(
            File.generated(
                config,
                source.relative_to(root).as_posix(),
                abs_src_path=str(source),
            )
        )
    license_text = (root / "LICENSE").read_text(encoding="utf-8").rstrip()
    files.append(
        File.generated(
            config,
            "license.md",
            content=f"# License\n\n```text\n{license_text}\n```\n",
        )
    )
    files.append(
        File.generated(
            config,
            "styles/code.css",
            content=HtmlFormatter().get_style_defs(".codehilite"),
        )
    )
    return files


def on_page_markdown(markdown, page, config, files):
    # MkDocs converts each page immediately after this hook.
    extension = next(
        extension for extension in config.markdown_extensions
        if isinstance(extension, RepositoryLinks)
    )
    extension.root = Path(config.config_file_path).resolve().parent
    extension.source = extension.root / page.file.src_uri
    extension.repo_url = config.repo_url.rstrip("/")
    extension.files = files
    return markdown


class RepositoryLinks(Extension):
    def extendMarkdown(self, md):
        # Rewrite repository links before MkDocs validates local link targets.
        md.treeprocessors.register(SourceLinks(md, self), "repository_links", 1)


class SourceLinks(Treeprocessor):
    def __init__(self, md, context):
        super().__init__(md)
        self.context = context

    def run(self, root):
        context = self.context
        for anchor in root.iter("a"):
            href = urlsplit(anchor.get("href", ""))
            if href.scheme or href.netloc or not href.path or href.path.startswith("/"):
                continue
            target = (context.source.parent / unquote(href.path)).resolve()
            if not target.is_relative_to(context.root) or not target.exists():
                continue
            relative = target.relative_to(context.root).as_posix()
            if relative == "LICENSE":
                path = Path(href.path).with_name("license.md").as_posix()
                anchor.set("href", urlunsplit(("", "", path, href.query, href.fragment)))
                continue
            if context.files.get_file_from_path(relative):
                continue
            view = "tree" if target.is_dir() else "blob"
            repo = urlsplit(context.repo_url)
            path = f"{repo.path}/{view}/main/{quote(relative)}"
            anchor.set("href", urlunsplit((repo.scheme, repo.netloc, path, href.query, href.fragment)))
