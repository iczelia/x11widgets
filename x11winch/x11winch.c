#define _GNU_SOURCE
#include "bg-add.png.h"
#include "bg.png.h"
#include "stickey.png.h"
#include "verdana.ttf.h"
#include <X11/Xatom.h>
#include <X11/Xft/Xft.h>
#include <X11/Xlib.h>
#include <X11/extensions/Xinerama.h>
#include <X11/extensions/Xrender.h>
#include <X11/keysym.h>
#include <png.h>

#include <freetype2/freetype/freetype.h>
#include <ft2build.h>

#include <fontconfig/fcfreetype.h>
#include <fontconfig/fontconfig.h>

#include <ctype.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#define MAX_CLIENTS 256
#define MAX_LABEL 512
#define FILTER_MAX 128
#define ANIM_STEPS 20
#define ANIM_TOTAL_MS 200

typedef struct {
  Window win;
  char label[MAX_LABEL];
  char title[MAX_LABEL];
  char execname[128];
  pid_t pid;
  int valid;
} Client;

typedef struct {
  Window win;
  int x, y, w, h;
  XftFont *xft_font;
  XftDraw *xft_draw;
  XftColor xft_color_text, xft_color_sel;
  FT_Library ft_lib;
  FT_Face ft_face;
  Pixmap bg_pixmap;
  Picture bg_picture;
  Picture win_picture;
  unsigned bg_w, bg_h;
} Overlay;

XftFont *xft_font_from_memory(Display *dpy, int screen,
                              const unsigned char *data, size_t len,
                              double pixel_size, FT_Library *out_lib,
                              FT_Face *out_face) {
  FT_Library lib = NULL;
  if (FT_Init_FreeType(&lib))
    return NULL;
  FT_Face face = NULL;
  if (FT_New_Memory_Face(lib, data, (FT_Long)len, 0, &face)) {
    FT_Done_FreeType(lib);
    return NULL;
  }
  FcPattern *pat =
      FcFreeTypeQueryFace(face, (const FcChar8 *)"memory", 0, NULL);
  if (!pat)
    return NULL;
  FcPatternDel(pat, FC_FILE);
  FcPatternDel(pat, FC_INDEX);
  FcPatternAddFTFace(pat, FC_FT_FACE, face);
  FcPatternAddBool(pat, FC_SCALABLE, FcTrue);
  FcPatternAddDouble(pat, FC_SIZE, pixel_size);
  FcConfigSubstitute(NULL, pat, FcMatchPattern);
  XftDefaultSubstitute(dpy, screen, pat);
  XftFont *xf = XftFontOpenPattern(dpy, pat);
  if (!xf) {
    FcPatternDestroy(pat);
    FT_Done_Face(face);
    FT_Done_FreeType(lib);
    return NULL;
  }
  if (out_lib)
    *out_lib = lib;
  else
    FT_Done_FreeType(lib);
  if (out_face)
    *out_face = face;
  else
    FT_Done_Face(face);
  return xf;
}

static Display *dpy;
static int screen;
static Window root;
static Atom net_client_list;
static Atom net_active_window;
static Atom net_wm_name;
static Atom utf8_string;
static Atom net_wm_pid;

static Client clients[MAX_CLIENTS];
static int client_count = 0;

static Overlay *overlays = NULL;
static int overlay_count = 0;

static int visible = 0;

/* shared background pixmap loaded once */
static Pixmap shared_bg_pixmap = 0;
static unsigned shared_bg_w = 0, shared_bg_h = 0;
/* selection (sticky) image loaded once */
static Pixmap shared_sel_pixmap = 0;
static unsigned shared_sel_w = 0, shared_sel_h = 0;
/* picture for the selection image (created in create_overlays) */
static Picture shared_sel_picture = 0;

/* additional overlay image (bottom-right decoration) loaded once */
static Pixmap shared_add_pixmap = 0;
static unsigned shared_add_w = 0, shared_add_h = 0;
static Picture shared_add_picture = 0;

static Colormap colormap;
static Visual *visual;
static int depth;

static char filter_text[FILTER_MAX] = {0};
static int filter_len = 0;
static int overlay_visible = 0;

/* index in clients[] of the currently highlighted item */
static int selected_index = 0;

static void set_font(Overlay *app) {
  if (!FcInit())
    exit(2);

  double pixel_size = 10.0;
  app->xft_font =
      xft_font_from_memory(dpy, screen, verdana_ttf, (size_t)verdana_ttf_len,
                           pixel_size, &app->ft_lib, &app->ft_face);
  if (!app->xft_font)
    exit(2);

  // Get the visual + colormap actually used by the window
  XWindowAttributes wa;
  XGetWindowAttributes(dpy, app->win, &wa);

  app->xft_draw = XftDrawCreate(dpy, app->win, wa.visual, wa.colormap);
  if (!app->xft_draw)
    exit(2);

  if (!XftColorAllocName(dpy, wa.visual, wa.colormap, "white",
                         &app->xft_color_text))
    exit(2);
  if (!XftColorAllocName(dpy, wa.visual, wa.colormap, "gray80",
                         &app->xft_color_sel))
    exit(2);
}

static void draw_gradient_border(int w, int h, Display *dpy, Window win) {
  if (w <= 1 || h <= 1)
    return;
  XRenderPictFormat *fmt = XRenderFindStandardFormat(dpy, PictStandardARGB32);
  if (!fmt)
    return;
  Picture dst = XRenderCreatePicture(dpy, win, fmt, 0, NULL);
  XFixed stops[2] = {XDoubleToFixed(0.0), XDoubleToFixed(1.0)};
  XRenderColor bw[2] = {{0, 0, 0, 0xffff}, {0xffff, 0xffff, 0xffff, 0xffff}};
  XRenderColor wb[2] = {{0xffff, 0xffff, 0xffff, 0xffff}, {0, 0, 0, 0xffff}};
  XLinearGradient lg;
  // top: black→white, left-to-right
  lg.p1.x = XDoubleToFixed(0);
  lg.p1.y = XDoubleToFixed(0);
  lg.p2.x = XDoubleToFixed(w);
  lg.p2.y = XDoubleToFixed(0);
  Picture p = XRenderCreateLinearGradient(dpy, &lg, stops, bw, 2);
  XRenderComposite(dpy, PictOpSrc, p, None, dst, 0, 0, 0, 0, 0, 0, w, 1);
  XRenderFreePicture(dpy, p);
  // bottom: white→black, left-to-right
  lg.p1.y = XDoubleToFixed(h - 1);
  lg.p2.y = XDoubleToFixed(h - 1);
  p = XRenderCreateLinearGradient(dpy, &lg, stops, wb, 2);
  XRenderComposite(dpy, PictOpSrc, p, None, dst, 0, 0, 0, 0, 0, h - 1, w, 1);
  XRenderFreePicture(dpy, p);
  // left: black→white, top-to-bottom
  lg.p1.x = XDoubleToFixed(0);
  lg.p1.y = XDoubleToFixed(0);
  lg.p2.x = XDoubleToFixed(0);
  lg.p2.y = XDoubleToFixed(h);
  p = XRenderCreateLinearGradient(dpy, &lg, stops, bw, 2);
  XRenderComposite(dpy, PictOpSrc, p, None, dst, 0, 0, 0, 0, 0, 0, 1, h);
  XRenderFreePicture(dpy, p);
  // right: white→black, top-to-bottom
  lg.p1.x = XDoubleToFixed(w - 1);
  lg.p1.y = XDoubleToFixed(0);
  lg.p2.x = XDoubleToFixed(w - 1);
  lg.p2.y = XDoubleToFixed(h);
  p = XRenderCreateLinearGradient(dpy, &lg, stops, wb, 2);
  XRenderComposite(dpy, PictOpSrc, p, None, dst, 0, 0, 0, 0, w - 1, 0, 1, h);
  XRenderFreePicture(dpy, p);
  XRenderFreePicture(dpy, dst);
}

static Pixmap load_png_to_pixmap_from_mem(Display *dpy, Drawable root,
                                          const unsigned char *buf, size_t len,
                                          unsigned *out_w, unsigned *out_h) {
  if (!buf || !len)
    return 0;

  png_image im;
  memset(&im, 0, sizeof im);
  im.version = PNG_IMAGE_VERSION;
  if (!png_image_begin_read_from_memory(&im, buf, len))
    return 0;
  im.format = PNG_FORMAT_RGBA;

  size_t sz = PNG_IMAGE_SIZE(im);
  png_bytep rgba = malloc(sz);
  if (!rgba) {
    png_image_free(&im);
    return 0;
  }
  if (!png_image_finish_read(&im, NULL, rgba, 0, NULL)) {
    free(rgba);
    png_image_free(&im);
    return 0;
  }

  const unsigned w = im.width, h = im.height;
  uint32_t *argb = malloc((size_t)w * h * 4);
  if (!argb) {
    free(rgba);
    png_image_free(&im);
    return 0;
  }
  for (size_t i = 0, n = (size_t)w * h; i < n; ++i) {
    uint8_t r = rgba[4 * i + 0], g = rgba[4 * i + 1], b = rgba[4 * i + 2],
            a = rgba[4 * i + 3];
    // premultiply
    r = (uint8_t)((r * (uint16_t)a + 127) / 255);
    g = (uint8_t)((g * (uint16_t)a + 127) / 255);
    b = (uint8_t)((b * (uint16_t)a + 127) / 255);
    argb[i] = ((uint32_t)a << 24) | ((uint32_t)r << 16) | ((uint32_t)g << 8) |
              (uint32_t)b;
  }
  free(rgba);
  png_image_free(&im);

  int fmt_count = 0;
  XPixmapFormatValues *pf = XListPixmapFormats(dpy, &fmt_count);
  int has32 = 0;
  for (int i = 0; i < fmt_count; ++i)
    if (pf[i].depth == 32) {
      has32 = 1;
      break;
    }
  if (pf)
    XFree(pf);
  if (!has32) {
    free(argb);
    return 0;
  }

  Pixmap pix = XCreatePixmap(dpy, root, w, h, 32);
  if (!pix) {
    free(argb);
    return 0;
  }

  XImage *xi = XCreateImage(dpy, DefaultVisual(dpy, DefaultScreen(dpy)), 32,
                            ZPixmap, 0, (char *)argb, w, h, 32, 0);
  if (!xi) {
    XFreePixmap(dpy, pix);
    free(argb);
    return 0;
  }
  xi->byte_order = ImageByteOrder(dpy); // let Xlib handle endianness

  GC gc = XCreateGC(dpy, pix, 0, NULL);
  XPutImage(dpy, pix, gc, xi, 0, 0, 0, 0, w, h);
  XFreeGC(dpy, gc);
  XDestroyImage(xi); // also frees argb

  if (out_w)
    *out_w = w;
  if (out_h)
    *out_h = h;
  return pix;
}

/* ---------- utils ---------- */

static unsigned long get_window_prop_window(Window w, Atom prop) {
  Atom actual_type;
  int actual_format;
  unsigned long nitems, bytes_after;
  unsigned char *prop_ret = NULL;
  unsigned long result = 0;
  if (Success == XGetWindowProperty(dpy, w, prop, 0, (~0L), False,
                                    AnyPropertyType, &actual_type,
                                    &actual_format, &nitems, &bytes_after,
                                    &prop_ret)) {
    if (nitems > 0) {
      result = ((Window *)prop_ret)[0];
    }
    if (prop_ret)
      XFree(prop_ret);
  }
  return result;
}

static int get_window_pid(Window w, pid_t *pid_out) {
  Atom actual_type;
  int actual_format;
  unsigned long nitems, bytes_after;
  unsigned char *prop_ret = NULL;
  if (Success == XGetWindowProperty(dpy, w, net_wm_pid, 0, 1, False,
                                    XA_CARDINAL, &actual_type, &actual_format,
                                    &nitems, &bytes_after, &prop_ret)) {
    if (nitems == 1) {
      *pid_out = *(pid_t *)prop_ret;
      XFree(prop_ret);
      return 1;
    }
    if (prop_ret)
      XFree(prop_ret);
  }
  return 0;
}

static void get_window_title(Window w, char *buf, size_t bufsz) {
  buf[0] = '\0';
  XTextProperty prop;
  if (XGetTextProperty(dpy, w, &prop, net_wm_name) && prop.value) {
    strncpy(buf, (char *)prop.value, bufsz - 1);
    buf[bufsz - 1] = '\0';
    XFree(prop.value);
    return;
  }
  XFetchName(dpy, w, &buf);
  if (!buf[0]) {
    snprintf(buf, bufsz, "(untitled)");
  }
}

static void read_proc_execname(pid_t pid, char *buf, size_t bufsz) {
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d/cmdline", (int)pid);
  int fd = open(path, O_RDONLY);
  if (fd >= 0) {
    char raw[4096];
    ssize_t n = read(fd, raw, sizeof(raw) - 1);
    close(fd);
    if (n > 0) {
      raw[n] = 0;
      /* cmdline: argv[0]\0argv[1]\0... choose argv[0] */
      char *argv0 = raw;
      if (*argv0) {
        char *base = strrchr(argv0, '/');
        if (base)
          base++;
        else
          base = argv0;
        strncpy(buf, base, bufsz - 1);
        buf[bufsz - 1] = 0;
        return;
      }
    }
  }

  /* fallback to comm */
  snprintf(path, sizeof(path), "/proc/%d/comm", (int)pid);
  fd = open(path, O_RDONLY);
  if (fd >= 0) {
    ssize_t n = read(fd, buf, bufsz - 1);
    close(fd);
    if (n > 0) {
      buf[n] = 0;
      char *p = strchr(buf, '\n');
      if (p)
        *p = 0;
      return;
    }
  }

  snprintf(buf, bufsz, "unknown");
}

static int strcasestr_simple(const char *hay, const char *needle) {
  if (!needle[0])
    return 1;
  size_t hl = strlen(hay);
  size_t nl = strlen(needle);
  for (size_t i = 0; i + nl <= hl; ++i) {
    size_t j = 0;
    for (; j < nl; ++j) {
      char c1 = tolower((unsigned char)hay[i + j]);
      char c2 = tolower((unsigned char)needle[j]);
      if (c1 != c2)
        break;
    }
    if (j == nl)
      return 1;
  }
  return 0;
}

/* ---------- clients / MRU ---------- */

static int ignore_badwindow(Display *d, XErrorEvent *e) {
  if (e->error_code == BadWindow)
    return 0;
  return 1;
}

static int safe_attrs(Display *dpy, Window w, XWindowAttributes *wa) {
  int (*old)(Display *, XErrorEvent *) = XSetErrorHandler(ignore_badwindow);
  int ok = XGetWindowAttributes(dpy, w, wa);
  XSync(dpy, False);
  XSetErrorHandler(old);
  return ok;
}

static int window_wants_ignored(Window w) {
  static Atom net_wm_state, net_wm_state_skip_taskbar;

  Atom actual_type;
  int actual_format;
  unsigned long nitems, bytes_after;
  unsigned char *prop_ret = NULL;
  int has = 0;

  if (!net_wm_state)
    net_wm_state = XInternAtom(dpy, "_NET_WM_STATE", False);
  if (!net_wm_state_skip_taskbar)
    net_wm_state_skip_taskbar =
        XInternAtom(dpy, "_NET_WM_STATE_SKIP_TASKBAR", False);

  if (Success == XGetWindowProperty(dpy, w, net_wm_state, 0, (~0L), False,
                                    AnyPropertyType, &actual_type,
                                    &actual_format, &nitems, &bytes_after,
                                    &prop_ret)) {
    Atom *atoms = (Atom *)prop_ret;
    for (unsigned long i = 0; i < nitems; ++i) {
      if (atoms[i] == net_wm_state_skip_taskbar) {
        has = 1;
        break;
      }
    }
  }
  if (prop_ret)
    XFree(prop_ret);
  return has;
}

static void rebuild_client_list(void) {
  client_count = 0;
  Atom actual_type;
  int actual_format;
  unsigned long nitems, bytes_after;
  unsigned char *prop_ret = NULL;

  if (Success == XGetWindowProperty(dpy, root, net_client_list, 0, (~0L), False,
                                    AnyPropertyType, &actual_type,
                                    &actual_format, &nitems, &bytes_after,
                                    &prop_ret)) {
    Window *wins = (Window *)prop_ret;
    for (unsigned long i = 0; i < nitems && client_count < MAX_CLIENTS; ++i) {
      Window w = wins[i];
      XWindowAttributes wa;
      if (!safe_attrs(dpy, w, &wa) || window_wants_ignored(w)) {
        continue;
      }
      clients[client_count].win = w;
      clients[client_count].valid = 1;
      clients[client_count].pid = 0;
      get_window_title(w, clients[client_count].title,
                       sizeof(clients[client_count].title));
      if (get_window_pid(w, &clients[client_count].pid)) {
        read_proc_execname(clients[client_count].pid,
                           clients[client_count].execname,
                           sizeof(clients[client_count].execname));
      } else {
        snprintf(clients[client_count].execname,
                 sizeof(clients[client_count].execname), "unknown");
      }
      snprintf(clients[client_count].label, sizeof(clients[client_count].label),
               "%d. %s - %s", client_count + 1, clients[client_count].execname,
               clients[client_count].title);
      client_count++;
    }
    if (prop_ret)
      XFree(prop_ret);
  }
}

/* move window to front of MRU */
static void mru_touch(Window w) {
  for (int i = 0; i < client_count; ++i) {
    if (clients[i].win == w) {
      if (i == 0)
        return;
      Client tmp = clients[i];
      memmove(&clients[1], &clients[0], sizeof(Client) * i);
      clients[0] = tmp;
      for (int j = 0; j < client_count; ++j) {
        snprintf(clients[j].label, sizeof(clients[j].label), "%d. %s - %s",
                 j + 1, clients[j].execname, clients[j].title);
      }
      return;
    }
  }
}

static void create_overlays(void) {
  int event_base, error_base;
  int screens = 1;
  XineramaScreenInfo *info = NULL;
  if (XineramaQueryExtension(dpy, &event_base, &error_base) &&
      XineramaIsActive(dpy)) {
    info = XineramaQueryScreens(dpy, &screens);
  }
  overlay_count = screens;
  overlays = calloc(screens, sizeof(Overlay));

  for (int i = 0; i < screens; ++i) {
    int sw = (info ? info[i].width : DisplayWidth(dpy, screen));
    int sh = (info ? info[i].height : DisplayHeight(dpy, screen));
    int sx = (info ? info[i].x_org : 0);
    int sy = (info ? info[i].y_org : 0);

    int w = sw * 0.3;
    int h = sh * 0.3;
    int x = sx + (sw - w) / 2;
    int y = sy + (sh - h) / 2;

    XSetWindowAttributes attr = {0};
    attr.override_redirect = True;
    attr.colormap = colormap;
    attr.border_pixel = 0;
    attr.background_pixel = 0;
    attr.event_mask =
        ExposureMask | KeyPressMask | KeyReleaseMask | StructureNotifyMask;

    Window win =
        XCreateWindow(dpy, root, x, y, w, h, 0, depth, InputOutput, visual,
                      CWOverrideRedirect | CWColormap | CWBorderPixel |
                          CWBackPixel | CWEventMask,
                      &attr);
    XSetWindowBackgroundPixmap(dpy, win, None);

    overlays[i].win = win;
    overlays[i].x = x;
    overlays[i].y = y;
    overlays[i].w = w;
    overlays[i].h = h;
    overlays[i].bg_pixmap = shared_bg_pixmap;
    overlays[i].bg_w = shared_bg_w;
    overlays[i].bg_h = shared_bg_h;
    overlays[i].bg_picture = 0;
    overlays[i].win_picture = 0;

    if (shared_bg_pixmap) {
      XRenderPictFormat *src_fmt =
          XRenderFindStandardFormat(dpy, PictStandardARGB32);
      if (src_fmt) {
        overlays[i].bg_picture =
            XRenderCreatePicture(dpy, shared_bg_pixmap, src_fmt, 0, NULL);
      }
      XRenderPictFormat *dst_fmt = XRenderFindVisualFormat(dpy, visual);
      if (dst_fmt) {
        overlays[i].win_picture =
            XRenderCreatePicture(dpy, overlays[i].win, dst_fmt, 0, NULL);
      }
      /* create a shared picture for the selection image once */
      if (shared_sel_pixmap && !shared_sel_picture) {
        XRenderPictFormat *sel_fmt =
            XRenderFindStandardFormat(dpy, PictStandardARGB32);
        if (sel_fmt) {
          shared_sel_picture =
              XRenderCreatePicture(dpy, shared_sel_pixmap, sel_fmt, 0, NULL);
        }
      }
      /* create a shared picture for the bottom-right add image once */
      if (shared_add_pixmap && !shared_add_picture) {
        XRenderPictFormat *add_fmt =
            XRenderFindStandardFormat(dpy, PictStandardARGB32);
        if (add_fmt) {
          shared_add_picture =
              XRenderCreatePicture(dpy, shared_add_pixmap, add_fmt, 0, NULL);
        }
      }
    }

    set_font(&overlays[i]);
  }

  if (info)
    XFree(info);
}

static void show_overlays(void) {
  /* create windows each time overlays are shown */
  create_overlays();

  int event_base, error_base;
  int screens = 1;
  XineramaScreenInfo *info = NULL;
  if (XineramaQueryExtension(dpy, &event_base, &error_base) &&
      XineramaIsActive(dpy)) {
    info = XineramaQueryScreens(dpy, &screens);
  }

  for (int i = 0; i < overlay_count; ++i) {
    int sw = (info ? info[i].width : DisplayWidth(dpy, screen));
    int sh = (info ? info[i].height : DisplayHeight(dpy, screen));
    int sx = (info ? info[i].x_org : 0);
    int sy = (info ? info[i].y_org : 0);
    int w = sw * 0.3;
    int h = sh * 0.3;
    int x = sx + (sw - w) / 2;
    int y = sy + (sh - h) / 2;

    XMoveResizeWindow(dpy, overlays[i].win, x, y, w, h);
    XMapRaised(dpy, overlays[i].win);

    overlays[i].x = x;
    overlays[i].y = y;
    overlays[i].w = w;
    overlays[i].h = h;

    if (overlays[i].bg_picture && overlays[i].win_picture && shared_bg_w &&
        shared_bg_h) {
      XTransform tr;
      double sx = (double)shared_bg_w / (double)w;
      double sy = (double)shared_bg_h / (double)h;
      memset(&tr, 0, sizeof(tr));
      tr.matrix[0][0] = XDoubleToFixed(sx);
      tr.matrix[1][1] = XDoubleToFixed(sy);
      tr.matrix[2][2] = XDoubleToFixed(1.0);
      XRenderSetPictureTransform(dpy, overlays[i].bg_picture, &tr);
      /* Use bilinear filtering for smoother scaling when available */
      XRenderSetPictureFilter(dpy, overlays[i].bg_picture, "bilinear", NULL, 0);

      XRenderComposite(dpy, PictOpSrc, overlays[i].bg_picture, None,
                       overlays[i].win_picture, 0, 0, 0, 0, 0, 0, overlays[i].w,
                       overlays[i].h);
    }
    XFlush(dpy);
  }

  /* grab keyboard so Tab etc. go to us */
  XGrabKeyboard(dpy, root, True, GrabModeAsync, GrabModeAsync, CurrentTime);

  overlay_visible = 1;
  selected_index = 0;

  if (info)
    XFree(info);
}

static void hide_overlays(void) {
  XUngrabKeyboard(dpy, CurrentTime);
  /* destroy windows and free overlay structures so they are recreated next time
   */
  for (int i = 0; i < overlay_count; ++i) {
    if (!overlays)
      break;
    if (overlays[i].win) {
      XUnmapWindow(dpy, overlays[i].win);
      if (overlays[i].bg_picture) {
        XRenderFreePicture(dpy, overlays[i].bg_picture);
        overlays[i].bg_picture = 0;
      }
      if (overlays[i].win_picture) {
        XRenderFreePicture(dpy, overlays[i].win_picture);
        overlays[i].win_picture = 0;
      }
      /* free shared selection picture once when tearing down overlays */
      if (shared_sel_picture) {
        XRenderFreePicture(dpy, shared_sel_picture);
        shared_sel_picture = 0;
      }
      /* free shared add-picture once when tearing down overlays */
      if (shared_add_picture) {
        XRenderFreePicture(dpy, shared_add_picture);
        shared_add_picture = 0;
      }
      XDestroyWindow(dpy, overlays[i].win);
      overlays[i].win = 0;
      // undo the opreations of set_font
      if (overlays[i].ft_face) {
        FT_Done_Face(overlays[i].ft_face);
        overlays[i].ft_face = NULL;
      }
      if (overlays[i].ft_lib) {
        FT_Done_FreeType(overlays[i].ft_lib);
        overlays[i].ft_lib = NULL;
      }
      if (overlays[i].xft_font) {
        XftFontClose(dpy, overlays[i].xft_font);
        overlays[i].xft_font = NULL;
      }
    }
  }
  free(overlays);
  overlays = NULL;
  overlay_count = 0;
  overlay_visible = 0;
}

static void reset_filter(void) {
  filter_text[0] = 0;
  filter_len = 0;
}

static int build_matches(int *out) {
  int c = 0;
  for (int i = 0; i < client_count; ++i) {
    if (strcasestr_simple(clients[i].label, filter_text)) {
      out[c++] = i;
    }
  }
  return c;
}

static void draw_overlay_contents(void) {
  if (!overlay_visible)
    return;

  int match_indices[MAX_CLIENTS];
  int match_count = build_matches(match_indices);

  int found = 0;
  for (int i = 0; i < match_count; ++i) {
    if (match_indices[i] == selected_index) {
      found = 1;
      break;
    }
  }
  if (!found) {
    selected_index = match_indices[0];
  }

  for (int o = 0; o < overlay_count; ++o) {
    Overlay *ov = &overlays[o];
    if (ov->bg_picture && ov->win_picture && ov->bg_w && ov->bg_h) {
      XTransform tr;
      double sx = (double)ov->bg_w / (double)ov->w;
      double sy = (double)ov->bg_h / (double)ov->h;
      memset(&tr, 0, sizeof(tr));
      tr.matrix[0][0] = XDoubleToFixed(sx);
      tr.matrix[1][1] = XDoubleToFixed(sy);
      tr.matrix[2][2] = XDoubleToFixed(1.0);
      XRenderSetPictureTransform(dpy, ov->bg_picture, &tr);
      /* Use bilinear filtering for smoother scaling when available */
      XRenderSetPictureFilter(dpy, ov->bg_picture, "bilinear", NULL, 0);

      XRenderComposite(dpy, PictOpSrc, ov->bg_picture, None, ov->win_picture, 0,
                       0, 0, 0, 0, 0, ov->w, ov->h);
    }

    if (shared_add_picture && ov->win_picture && shared_add_w && shared_add_h) {
      int margin = 5;
      int dest_w = (int)shared_add_w;
      int dest_h = (int)shared_add_h;
      int dest_x = ov->w - dest_w - margin;
      int dest_y = ov->h - dest_h - margin;
      if (dest_x < 0)
        dest_x = 0;
      if (dest_y < 0)
        dest_y = 0;
      /* No transform: draw source at its native size into dest rectangle */
      XRenderComposite(dpy, PictOpOver, shared_add_picture, None,
                       ov->win_picture, 0, 0, 0, 0, dest_x, dest_y, dest_w,
                       dest_h);
    }

    int y = 20;
    char filterline[256];
    snprintf(filterline, sizeof(filterline), "filter: %s", filter_text);
    XftDrawStringUtf8(ov->xft_draw, &ov->xft_color_text, ov->xft_font, 10, y,
                      (FcChar8 *)filterline, strlen(filterline));
    y += ov->xft_font->ascent + 10;

    int to_show = match_count < 15 ? match_count : 15;
    for (int i = 0; i < to_show; ++i) {
      int idx = match_indices[i];
      char *txt = clients[idx].label;
      int is_sel = (idx == selected_index);
      int x = 10;
      if (is_sel) {
        int dest_x = 5;
        int dest_y = y - ov->xft_font->ascent;
        int dest_w = ov->w - 10;
        int dest_h = ov->xft_font->ascent + ov->xft_font->descent + 4;
        if (shared_sel_picture && ov->win_picture && shared_sel_w &&
            shared_sel_h) {
          /* set transform so source image scales to dest_w x dest_h */
          XTransform tr;
          double sx = (double)shared_sel_w / (double)dest_w;
          double sy = (double)shared_sel_h / (double)dest_h;
          memset(&tr, 0, sizeof(tr));
          tr.matrix[0][0] = XDoubleToFixed(sx);
          tr.matrix[1][1] = XDoubleToFixed(sy);
          tr.matrix[2][2] = XDoubleToFixed(1.0);
          XRenderSetPictureTransform(dpy, shared_sel_picture, &tr);
          XRenderSetPictureFilter(dpy, shared_sel_picture, "bilinear", NULL, 0);
          XRenderComposite(dpy, PictOpOver, shared_sel_picture, None,
                           ov->win_picture, 0, 0, 0, 0, dest_x, dest_y, dest_w,
                           dest_h);
        }

        XftDrawStringUtf8(ov->xft_draw, &ov->xft_color_sel, ov->xft_font, x + 5,
                          y, (FcChar8 *)txt, strlen(txt));
      } else {
        XftDrawStringUtf8(ov->xft_draw, &ov->xft_color_text, ov->xft_font, x, y,
                          (FcChar8 *)txt, strlen(txt));
      }
      y += ov->xft_font->ascent + ov->xft_font->descent + 4;
    }
    draw_gradient_border(ov->w, ov->h, dpy, ov->win);
    XFlush(dpy);
  }
}

static void select_next(int dir) {
  int match_indices[MAX_CLIENTS];
  int match_count = build_matches(match_indices);
  if (match_count == 0)
    return;
  int pos = 0;
  for (int i = 0; i < match_count; ++i) {
    if (match_indices[i] == selected_index) {
      pos = i;
      break;
    }
  }
  pos = (pos + dir + match_count) % match_count;
  selected_index = match_indices[pos];
  draw_overlay_contents();
}

static void animate_shrink(void) {
  const int steps = ANIM_STEPS;
  const int sleep_us = ANIM_TOTAL_MS * 1000 / steps;

  for (int s = 0; s < steps; ++s) {
    double f = 1.0 - (double)(s + 1) / steps;
    for (int o = 0; o < overlay_count; ++o) {
      Overlay *ov = &overlays[o];
      if (!ov || !ov->win)
        continue;
      XWindowAttributes xa;
      if (!XGetWindowAttributes(dpy, ov->win, &xa))
        continue;
      if (xa.map_state == IsUnmapped)
        continue;

      int nw = (int)(ov->w * f);
      int nh = (int)(ov->h * f);
      if (nw < 20)
        nw = 20;
      if (nh < 20)
        nh = 20;
      int nx = ov->x + (ov->w - nw) / 2;
      int ny = ov->y + (ov->h - nh) / 2;

      XMoveResizeWindow(dpy, ov->win, nx, ny, nw, nh);
    }
    XSync(dpy, False);
    usleep(sleep_us);
  }
}

static void activate_window(Window w) {
  if (!w)
    return;

  XEvent e;
  memset(&e, 0, sizeof(e));
  e.xclient.type = ClientMessage;
  e.xclient.window = w;
  e.xclient.message_type = XInternAtom(dpy, "_NET_ACTIVE_WINDOW", False);
  e.xclient.format = 32;
  e.xclient.data.l[0] = 1;
  e.xclient.data.l[1] = CurrentTime;
  e.xclient.data.l[2] = 0;
  e.xclient.data.l[3] = 0;
  e.xclient.data.l[4] = 0;

  XSendEvent(dpy, root, False,
             SubstructureRedirectMask | SubstructureNotifyMask, &e);

  XWindowAttributes attr;
  if (XGetWindowAttributes(dpy, w, &attr) != 0 &&
      attr.map_state != IsUnmapped) {
    XRaiseWindow(dpy, w);
    XSetInputFocus(dpy, w, RevertToPointerRoot, CurrentTime);
  }
}

int main(int argc, char **argv) {
  dpy = XOpenDisplay(NULL);
  if (!dpy)
    _exit(1);

  screen = DefaultScreen(dpy);
  root = RootWindow(dpy, screen);

  XVisualInfo vinfo;
  if (!XMatchVisualInfo(dpy, screen, 32, TrueColor, &vinfo)) {
    fprintf(stderr, "No 32-bit TrueColor visual on this screen\n");
    exit(1);
  }

  /* Verify the visual has an alpha channel for per-pixel opacity */
  XRenderPictFormat *fmt = XRenderFindVisualFormat(dpy, vinfo.visual);
  if (!fmt || fmt->type != PictTypeDirect || fmt->direct.alphaMask == 0) {
    fprintf(stderr, "32-bit visual lacks ARGB alpha support\n");
    exit(1);
  }

  Colormap cmap =
      XCreateColormap(dpy, RootWindow(dpy, screen), vinfo.visual, AllocNone);

  depth = vinfo.depth;
  visual = vinfo.visual;
  colormap = cmap;

  net_client_list = XInternAtom(dpy, "_NET_CLIENT_LIST", False);
  net_active_window = XInternAtom(dpy, "_NET_ACTIVE_WINDOW", False);
  net_wm_name = XInternAtom(dpy, "_NET_WM_NAME", False);
  utf8_string = XInternAtom(dpy, "UTF8_STRING", False);
  net_wm_pid = XInternAtom(dpy, "_NET_WM_PID", False);

  KeyCode tab_code = XKeysymToKeycode(dpy, XK_Tab);
  XGrabKey(dpy, tab_code, Mod1Mask, root, True, GrabModeAsync, GrabModeAsync);

  XSelectInput(dpy, root,
               SubstructureNotifyMask | PropertyChangeMask | KeyPressMask |
                   KeyReleaseMask);

  shared_bg_pixmap = load_png_to_pixmap_from_mem(
      dpy, root, bg_png, sizeof(bg_png), &shared_bg_w, &shared_bg_h);
  shared_sel_pixmap = load_png_to_pixmap_from_mem(dpy, root, stickey_png,
                                                  (size_t)stickey_png_len,
                                                  &shared_sel_w, &shared_sel_h);
  shared_add_pixmap =
      load_png_to_pixmap_from_mem(dpy, root, bg_add_png, (size_t)bg_add_png_len,
                                  &shared_add_w, &shared_add_h);
  rebuild_client_list();

  for (;;) {
    XEvent ev;
    XNextEvent(dpy, &ev);

    switch (ev.type) {
    case KeyPress: {
      XKeyEvent *ke = &ev.xkey;
      KeySym ks = XLookupKeysym(ke, 0);

      if (ke->root == root && ks == XK_Tab && (ke->state & Mod1Mask) &&
          !visible) {
        reset_filter();
        show_overlays();
        draw_overlay_contents();
        visible = 1;
        break;
      }

      if (overlay_visible) {
        if (ks == XK_Escape) {
          animate_shrink();
          hide_overlays();
          reset_filter();
          visible = 0;
        } else if (ks == XK_Return) {
          animate_shrink();
          hide_overlays();
          activate_window(clients[selected_index].win);
          mru_touch(clients[selected_index].win);
          reset_filter();
          visible = 0;
        } else if (ks == XK_Tab && (ke->state & ShiftMask)) {
          select_next(-1);
        } else if (ks == XK_Tab) {
          select_next(+1);
        } else if (ks == XK_Down) {
          select_next(+1);
        } else if (ks == XK_Up) {
          select_next(-1);
        } else if (ks == XK_BackSpace) {
          if (filter_len > 0) {
            filter_text[--filter_len] = 0;
            /* after filter changes, reset selection to first match */
            int match_indices[MAX_CLIENTS];
            int mc = build_matches(match_indices);
            selected_index = match_indices[0];
            draw_overlay_contents();
          }
        } else {
          /* printable → filter */
          char buf[8];
          int n = XLookupString(ke, buf, sizeof(buf), NULL, NULL);
          if (n > 0) {
            for (int i = 0; i < n; ++i) {
              if (filter_len < FILTER_MAX - 1 && buf[i] >= 32 && buf[i] < 127) {
                filter_text[filter_len++] = buf[i];
              }
            }
            filter_text[filter_len] = 0;
            int match_indices[MAX_CLIENTS];
            int mc = build_matches(match_indices);
            if (mc == 0) {
              selected_index = -1;
              reset_filter();
              draw_overlay_contents();
            } else {
              selected_index = match_indices[0];
              draw_overlay_contents();
              /* auto-select if only one */
              if (mc == 1) {
                animate_shrink();
                hide_overlays();
                activate_window(clients[selected_index].win);
                mru_touch(clients[selected_index].win);
                reset_filter();
                visible = 0;
              }
            }
          }
        }
      }

    } break;
    case PropertyNotify: {
      XPropertyEvent *pe = &ev.xproperty;
      if (pe->window == root && pe->atom == net_client_list) {
        rebuild_client_list();
        if (overlay_visible)
          draw_overlay_contents();
      } else if (pe->window == root && pe->atom == net_active_window) {
        Window aw = get_window_prop_window(root, net_active_window);
        if (aw) {
          mru_touch(aw);
          if (overlay_visible)
            draw_overlay_contents();
        }
      }
    } break;
    case Expose: {
      if (overlay_visible)
        draw_overlay_contents();
    } break;
    case DestroyNotify:
    case UnmapNotify: {
      rebuild_client_list();
      if (overlay_visible)
        draw_overlay_contents();
    } break;
    default:
      break;
    }
  }

  return 0;
}
