bl_info = {
    "name": "Pixel Column Printer",
    "author": "TrailPrint3D",
    "version": (0, 2, 0),
    "blender": (4, 2, 0),
    "location": "View3D > Sidebar > Pixel Columns",
    "description": "Render JPG images as coarse RGB, CMYK, or BW 3D printable color columns.",
    "category": "Object",
    "support": "COMMUNITY",
}

import logging
import math
import os
import random
from datetime import datetime
from logging.handlers import RotatingFileHandler

import bpy  # type: ignore


LOGGER_NAME = "PixelColumnPrinter"
ROOT_COLLECTION_NAME = "Pixel Column Printer"
TEMP_COLLECTION_NAME = "Temporary Objects"
GENERATED_COLLECTION_NAME = "Generated Columns"

module_logger = logging.getLogger(LOGGER_NAME)
module_logger.addHandler(logging.NullHandler())
module_logger.propagate = False


def _abs_path(path):
    return bpy.path.abspath(path) if path else ""


def _resolve_log_path(props):
    requested = _abs_path(props.pcp_log_file)
    if requested:
        folder = os.path.dirname(requested)
        if folder and os.path.isdir(folder):
            return requested
    image_dir = os.path.dirname(_abs_path(props.pcp_image_path))
    if image_dir and os.path.isdir(image_dir):
        return os.path.join(image_dir, "pixel_column_printer.log")
    temp_dir = bpy.app.tempdir or bpy.utils.user_resource("TEMP")
    return os.path.join(temp_dir, "pixel_column_printer.log")


def init_module_logger(context=None):
    props = getattr(context.scene, "pcp", None) if context and getattr(context, "scene", None) else None
    if props is None:
        return module_logger

    for handler in list(module_logger.handlers):
        if isinstance(handler, RotatingFileHandler):
            module_logger.removeHandler(handler)
            handler.close()

    enabled = getattr(props, "pcp_debug_logging_enabled", False)
    level = getattr(logging, getattr(props, "pcp_debug_log_level", "INFO"), logging.INFO)
    module_logger.setLevel(level if enabled else logging.CRITICAL + 1)

    if enabled:
        log_path = _resolve_log_path(props)
        handler = RotatingFileHandler(log_path, maxBytes=2 * 1024 * 1024, backupCount=3, encoding="utf-8")
        handler.setLevel(level)
        handler.setFormatter(logging.Formatter("%(asctime)s | %(levelname)s | %(funcName)s | %(message)s"))
        module_logger.addHandler(handler)
        module_logger.info("Logger initialized at %s", log_path)
    return module_logger


def logging_settings_update(self, context):
    init_module_logger(context)


def _ensure_child_collection(parent, name):
    collection = bpy.data.collections.get(name)
    if collection is None:
        collection = bpy.data.collections.new(name)
    if collection.name not in parent.children.keys():
        parent.children.link(collection)
    return collection


def get_collections(scene):
    root = bpy.data.collections.get(ROOT_COLLECTION_NAME)
    if root is None:
        root = bpy.data.collections.new(ROOT_COLLECTION_NAME)
    if root.name not in scene.collection.children.keys():
        scene.collection.children.link(root)
    generated = _ensure_child_collection(root, GENERATED_COLLECTION_NAME)
    temp = _ensure_child_collection(root, TEMP_COLLECTION_NAME)
    return root, generated, temp


def clear_collection(collection):
    for obj in list(collection.objects):
        bpy.data.objects.remove(obj, do_unlink=True)
    for child in list(collection.children):
        clear_collection(child)
        bpy.data.collections.remove(child)


def make_material(name, color):
    material = bpy.data.materials.get(name)
    if material is None:
        material = bpy.data.materials.new(name)
    material.diffuse_color = color
    return material


def get_materials():
    return {
        "RED": make_material("PCP Red", (1.0, 0.02, 0.02, 1.0)),
        "GREEN": make_material("PCP Green", (0.02, 0.75, 0.08, 1.0)),
        "BLUE": make_material("PCP Blue", (0.02, 0.18, 1.0, 1.0)),
        "CYAN": make_material("PCP Cyan", (0.0, 0.75, 1.0, 1.0)),
        "MAGENTA": make_material("PCP Magenta", (1.0, 0.0, 0.72, 1.0)),
        "YELLOW": make_material("PCP Yellow", (1.0, 0.86, 0.02, 1.0)),
        "BLACK": make_material("PCP Black", (0.015, 0.015, 0.015, 1.0)),
        "WHITE": make_material("PCP White", (0.94, 0.94, 0.9, 1.0)),
        "BASE": make_material("PCP Baseplate", (0.55, 0.55, 0.55, 1.0)),
        "LABEL": make_material("PCP Label", (0.05, 0.05, 0.05, 1.0)),
    }


def load_image_pixels(path):
    image = bpy.data.images.load(path, check_existing=False)
    image_width, image_height = image.size
    pixels = list(image.pixels[:])
    return image, int(image_width), int(image_height), pixels


def average_block(pixels, image_width, image_height, x0, y0, x1, y1):
    red = green = blue = count = 0.0
    ix0 = max(0, min(image_width - 1, x0))
    ix1 = max(ix0 + 1, min(image_width, x1))
    iy0 = max(0, min(image_height - 1, y0))
    iy1 = max(iy0 + 1, min(image_height, y1))

    for y in range(iy0, iy1):
        row = y * image_width * 4
        for x in range(ix0, ix1):
            idx = row + x * 4
            red += pixels[idx]
            green += pixels[idx + 1]
            blue += pixels[idx + 2]
            count += 1.0

    if count <= 0:
        return 0.0, 0.0, 0.0
    return red / count, green / count, blue / count


def rgb_to_cmyk(red, green, blue):
    black = 1.0 - max(red, green, blue)
    if black >= 0.999:
        return 0.0, 0.0, 0.0, 1.0
    cyan = (1.0 - red - black) / (1.0 - black)
    magenta = (1.0 - green - black) / (1.0 - black)
    yellow = (1.0 - blue - black) / (1.0 - black)
    return cyan, magenta, yellow, black


def channel_values(props, red, green, blue):
    if props.pcp_color_mode == "CMYK":
        names = ("CYAN", "MAGENTA", "YELLOW", "BLACK")
        values = rgb_to_cmyk(red, green, blue)
    elif props.pcp_color_mode == "BW":
        luminance = red * 0.2126 + green * 0.7152 + blue * 0.0722
        names = ("WHITE", "BLACK")
        values = (luminance, 1.0 - luminance)
    else:
        names = ("RED", "GREEN", "BLUE")
        values = (red, green, blue)

    if props.pcp_normalize_channel_thickness:
        total = sum(values)
        if total > 0:
            values = tuple(value / total for value in values)
    return tuple(zip(names, values))


def rectangle_mesh(name, width, depth, height):
    hw = width * 0.5
    hd = depth * 0.5
    verts = [
        (-hw, -hd, 0.0),
        (hw, -hd, 0.0),
        (hw, hd, 0.0),
        (-hw, hd, 0.0),
        (-hw, -hd, height),
        (hw, -hd, height),
        (hw, hd, height),
        (-hw, hd, height),
    ]
    faces = [(0, 1, 2, 3), (4, 7, 6, 5), (0, 4, 5, 1), (1, 5, 6, 2), (2, 6, 7, 3), (3, 7, 4, 0)]
    mesh = bpy.data.meshes.new(name)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    return mesh


def prism_mesh(name, radius, height, sides):
    bottom = []
    top = []
    verts = []
    for index in range(sides):
        angle = (math.tau * index / sides) + (math.pi / 6.0 if sides == 6 else 0.0)
        bottom.append(len(verts))
        verts.append((math.cos(angle) * radius, math.sin(angle) * radius, 0.0))
    for index in range(sides):
        angle = (math.tau * index / sides) + (math.pi / 6.0 if sides == 6 else 0.0)
        top.append(len(verts))
        verts.append((math.cos(angle) * radius, math.sin(angle) * radius, height))

    faces = [tuple(reversed(bottom)), tuple(top)]
    for index in range(sides):
        faces.append((bottom[index], bottom[(index + 1) % sides], top[(index + 1) % sides], top[index]))
    mesh = bpy.data.meshes.new(name)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    return mesh


def create_object(name, mesh, collection, material, location):
    obj = bpy.data.objects.new(name, mesh)
    obj.location = location
    obj.data.materials.append(material)
    collection.objects.link(obj)
    return obj


def create_column_segment(name, props, value, material, collection, center_x, center_y, width, depth, rng, pixel_jitter=0.0):
    min_fraction = max(0.0, min(0.95, props.pcp_min_channel_fraction))
    footprint_value = max(min_fraction, value)
    height_value = value if props.pcp_height_from_color_amount else 1.0
    height = props.pcp_column_height + props.pcp_color_height_scale * height_value
    height += pixel_jitter
    height += rng.uniform(-props.pcp_subpixel_height_jitter, props.pcp_subpixel_height_jitter)
    height = max(props.pcp_min_column_height, height)

    if props.pcp_column_shape == "SQUARE":
        mesh = rectangle_mesh(name + " Mesh", width, depth, height)
    else:
        radius = min(width, depth) * 0.5 * max(0.05, footprint_value)
        sides = 32 if props.pcp_column_shape == "CIRCLE" else 6
        mesh = prism_mesh(name + " Mesh", radius, height, sides)
    return create_object(name, mesh, collection, material, (center_x, center_y, props.pcp_baseplate_thickness))


def create_baseplate(props, collection, material, columns_x, columns_y):
    width = columns_x * props.pcp_pixel_width + props.pcp_edge_extension * 2.0
    depth = columns_y * props.pcp_pixel_width + props.pcp_edge_extension * 2.0
    mesh = rectangle_mesh("Pixel Column Baseplate Mesh", width, depth, props.pcp_baseplate_thickness)
    obj = create_object("Pixel Column Baseplate", mesh, collection, material, (0.0, 0.0, 0.0))
    return obj, width, depth


def create_labels(props, collection, materials, base_width, base_depth):
    if not props.pcp_include_labels:
        return []

    labels = []
    source_name = os.path.splitext(os.path.basename(_abs_path(props.pcp_image_path)))[0]
    text = props.pcp_label_text.strip() or source_name or "Pixel Columns"
    label_specs = [
        (text, (0.0, -base_depth * 0.5 + props.pcp_edge_extension * 0.35, props.pcp_baseplate_thickness + 0.02), 0.0),
        (props.pcp_color_mode, (-base_width * 0.5 + props.pcp_edge_extension * 0.35, 0.0, props.pcp_baseplate_thickness + 0.02), math.radians(90.0)),
    ]

    for index, (body, location, rotation_z) in enumerate(label_specs, start=1):
        font_curve = bpy.data.curves.new(f"Pixel Column Label {index}", "FONT")
        font_curve.body = body
        font_curve.align_x = "CENTER"
        font_curve.align_y = "CENTER"
        font_curve.size = props.pcp_label_size
        font_curve.extrude = props.pcp_label_emboss_height
        obj = bpy.data.objects.new(f"Pixel Column Label {index}", font_curve)
        obj.location = location
        obj.rotation_euler[2] = rotation_z
        obj.data.materials.append(materials["LABEL"])
        collection.objects.link(obj)
        labels.append(obj)
    return labels


class PCP_Properties(bpy.types.PropertyGroup):
    pcp_image_path: bpy.props.StringProperty(
        name="JPG Image",
        description="Input JPG image to turn into 3D-printable pixel columns",
        subtype="FILE_PATH",
    )
    pcp_color_mode: bpy.props.EnumProperty(
        name="Color Selection",
        items=(
            ("RGB", "RGB", "Use red, green, and blue sub-columns"),
            ("CMYK", "CMYK", "Use cyan, magenta, yellow, and black sub-columns"),
            ("BW", "BW", "Use white and black sub-columns"),
        ),
        default="RGB",
    )
    pcp_column_shape: bpy.props.EnumProperty(
        name="Column Shape",
        items=(
            ("CIRCLE", "Circle", "Round vertical columns"),
            ("SQUARE", "Square", "Rectangular sub-columns that fill each pixel cell"),
            ("HEX", "Hex", "Hexagonal vertical columns"),
        ),
        default="SQUARE",
    )
    pcp_pixel_width: bpy.props.FloatProperty(name="Pixel Width", default=3.0, min=0.1, unit="LENGTH")
    pcp_output_width_pixels: bpy.props.IntProperty(name="Pixel Density", default=48, min=1, max=400)
    pcp_preserve_aspect_ratio: bpy.props.BoolProperty(name="Preserve Aspect Ratio", default=True)
    pcp_output_height_pixels: bpy.props.IntProperty(name="Manual Height Pixels", default=48, min=1, max=400)
    pcp_column_height: bpy.props.FloatProperty(name="Base Column Height", default=4.0, min=0.05, unit="LENGTH")
    pcp_color_height_scale: bpy.props.FloatProperty(name="Color Height Scale", default=3.0, min=0.0, unit="LENGTH")
    pcp_min_column_height: bpy.props.FloatProperty(name="Minimum Column Height", default=0.6, min=0.01, unit="LENGTH")
    pcp_height_from_color_amount: bpy.props.BoolProperty(name="Color Amount Affects Height", default=True)
    pcp_normalize_channel_thickness: bpy.props.BoolProperty(name="Normalize Channel Thickness", default=True)
    pcp_min_channel_fraction: bpy.props.FloatProperty(name="Minimum Channel Thickness", default=0.03, min=0.0, max=0.95)
    pcp_pixel_height_jitter: bpy.props.FloatProperty(name="Pixel Height Variation", default=0.0, min=0.0, unit="LENGTH")
    pcp_subpixel_height_jitter: bpy.props.FloatProperty(name="Sub-Pixel Height Variation", default=0.0, min=0.0, unit="LENGTH")
    pcp_random_seed: bpy.props.IntProperty(name="Random Seed", default=42, min=0)
    pcp_baseplate_thickness: bpy.props.FloatProperty(name="Baseplate Thickness", default=1.2, min=0.05, unit="LENGTH")
    pcp_edge_extension: bpy.props.FloatProperty(name="Edge Extension", default=6.0, min=0.0, unit="LENGTH")
    pcp_include_labels: bpy.props.BoolProperty(name="Edge Labels", default=True)
    pcp_label_text: bpy.props.StringProperty(name="Label Text", default="")
    pcp_label_size: bpy.props.FloatProperty(name="Label Size", default=3.0, min=0.1, unit="LENGTH")
    pcp_label_emboss_height: bpy.props.FloatProperty(name="Label Emboss Height", default=0.35, min=0.0, unit="LENGTH")
    pcp_clear_previous: bpy.props.BoolProperty(name="Clear Previous Generated Objects", default=True)
    pcp_debug_logging_enabled: bpy.props.BoolProperty(name="Detailed Logging", default=False, update=logging_settings_update)
    pcp_debug_log_level: bpy.props.EnumProperty(
        name="Log Level",
        items=(("DEBUG", "Debug", ""), ("INFO", "Info", ""), ("WARNING", "Warning", ""), ("ERROR", "Error", "")),
        default="INFO",
        update=logging_settings_update,
    )
    pcp_log_file: bpy.props.StringProperty(name="Log File", subtype="FILE_PATH", default="", update=logging_settings_update)


class PCP_OT_generate(bpy.types.Operator):
    bl_idname = "pcp.generate_columns"
    bl_label = "Generate Pixel Columns"
    bl_description = "Read the selected JPG, pixelate it, and create 3D printable color columns"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        props = context.scene.pcp
        log = init_module_logger(context)
        path = _abs_path(props.pcp_image_path)
        if not path or not os.path.isfile(path):
            self.report({"ERROR"}, "Choose a valid JPG image path.")
            return {"CANCELLED"}

        _root_collection, generated_collection, temp_collection = get_collections(context.scene)
        if props.pcp_clear_previous:
            log.info("Clearing previous generated and temporary objects")
            clear_collection(generated_collection)
            clear_collection(temp_collection)

        run_name = datetime.now().strftime("Run %Y%m%d_%H%M%S")
        run_collection = _ensure_child_collection(generated_collection, run_name)
        temp_run_collection = _ensure_child_collection(temp_collection, run_name)
        log.info("Using generated collection %s and temporary collection %s", run_collection.name, temp_run_collection.name)

        try:
            image, image_width, image_height, pixels = load_image_pixels(path)
        except Exception as exc:
            log.exception("Could not load image")
            self.report({"ERROR"}, f"Could not load image: {exc}")
            return {"CANCELLED"}

        materials = get_materials()
        columns_x = props.pcp_output_width_pixels
        if props.pcp_preserve_aspect_ratio:
            columns_y = max(1, round(columns_x * image_height / image_width))
        else:
            columns_y = props.pcp_output_height_pixels
        rng = random.Random(props.pcp_random_seed)

        log.info("Generating %sx%s coarse pixels from %sx%s image", columns_x, columns_y, image_width, image_height)
        _baseplate, base_width, base_depth = create_baseplate(props, run_collection, materials["BASE"], columns_x, columns_y)
        create_labels(props, run_collection, materials, base_width, base_depth)

        origin_x = -columns_x * props.pcp_pixel_width * 0.5
        origin_y = -columns_y * props.pcp_pixel_width * 0.5
        created_segments = 0

        for py in range(columns_y):
            src_y0 = int(py * image_height / columns_y)
            src_y1 = int((py + 1) * image_height / columns_y)
            pixel_jitter = rng.uniform(-props.pcp_pixel_height_jitter, props.pcp_pixel_height_jitter)

            for px in range(columns_x):
                src_x0 = int(px * image_width / columns_x)
                src_x1 = int((px + 1) * image_width / columns_x)
                red, green, blue = average_block(pixels, image_width, image_height, src_x0, src_y0, src_x1, src_y1)
                channels = channel_values(props, red, green, blue)
                count = len(channels)
                cell_x = origin_x + (px + 0.5) * props.pcp_pixel_width
                cell_y = origin_y + (columns_y - py - 0.5) * props.pcp_pixel_width

                if props.pcp_column_shape == "SQUARE":
                    running_x = cell_x - props.pcp_pixel_width * 0.5
                    channel_total = sum(max(props.pcp_min_channel_fraction, value) for _, value in channels)
                    for channel_name, value in channels:
                        fraction = max(props.pcp_min_channel_fraction, value) / channel_total
                        segment_width = props.pcp_pixel_width * fraction
                        center_x = running_x + segment_width * 0.5
                        running_x += segment_width
                        create_column_segment(
                            f"Pixel {px:03d}-{py:03d} {channel_name}",
                            props,
                            value,
                            materials[channel_name],
                            run_collection,
                            center_x,
                            cell_y,
                            segment_width,
                            props.pcp_pixel_width,
                            rng,
                            pixel_jitter,
                        )
                        created_segments += 1
                else:
                    spacing = props.pcp_pixel_width / count
                    for index, (channel_name, value) in enumerate(channels):
                        center_x = cell_x - props.pcp_pixel_width * 0.5 + spacing * (index + 0.5)
                        create_column_segment(
                            f"Pixel {px:03d}-{py:03d} {channel_name}",
                            props,
                            value,
                            materials[channel_name],
                            run_collection,
                            center_x,
                            cell_y,
                            spacing * 0.9,
                            props.pcp_pixel_width * 0.9,
                            rng,
                            pixel_jitter,
                        )
                        created_segments += 1

        temp_marker_mesh = rectangle_mesh("Pixel Column Temp Marker Mesh", 0.2, 0.2, 0.2)
        temp_marker = create_object("Last Generation Temp Marker", temp_marker_mesh, temp_run_collection, materials["BASE"], (0, 0, 0))
        temp_marker.hide_viewport = True
        temp_marker.hide_render = True

        try:
            bpy.data.images.remove(image)
        except ReferenceError:
            pass

        log.info("Created baseplate plus %s column segments", created_segments)
        self.report({"INFO"}, f"Created {columns_x} x {columns_y} pixels ({created_segments} color columns).")
        return {"FINISHED"}


class PCP_PT_main_panel(bpy.types.Panel):
    bl_label = "Pixel Column Printer"
    bl_idname = "PCP_PT_main_panel"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "Pixel Columns"

    def draw(self, context):
        layout = self.layout
        props = context.scene.pcp

        layout.operator(PCP_OT_generate.bl_idname, icon="MESH_CUBE")

        image_box = layout.box()
        image_box.label(text="Image")
        image_box.prop(props, "pcp_image_path")
        image_box.prop(props, "pcp_color_mode")
        image_box.prop(props, "pcp_column_shape")
        image_box.prop(props, "pcp_output_width_pixels")
        image_box.prop(props, "pcp_preserve_aspect_ratio")
        if not props.pcp_preserve_aspect_ratio:
            image_box.prop(props, "pcp_output_height_pixels")

        geometry_box = layout.box()
        geometry_box.label(text="Geometry")
        geometry_box.prop(props, "pcp_pixel_width")
        geometry_box.prop(props, "pcp_column_height")
        geometry_box.prop(props, "pcp_height_from_color_amount")
        geometry_box.prop(props, "pcp_color_height_scale")
        geometry_box.prop(props, "pcp_min_column_height")
        geometry_box.prop(props, "pcp_normalize_channel_thickness")
        geometry_box.prop(props, "pcp_min_channel_fraction")

        texture_box = layout.box()
        texture_box.label(text="Texture")
        texture_box.prop(props, "pcp_pixel_height_jitter")
        texture_box.prop(props, "pcp_subpixel_height_jitter")
        texture_box.prop(props, "pcp_random_seed")

        base_box = layout.box()
        base_box.label(text="Baseplate")
        base_box.prop(props, "pcp_baseplate_thickness")
        base_box.prop(props, "pcp_edge_extension")
        base_box.prop(props, "pcp_include_labels")
        if props.pcp_include_labels:
            base_box.prop(props, "pcp_label_text")
            base_box.prop(props, "pcp_label_size")
            base_box.prop(props, "pcp_label_emboss_height")

        logging_box = layout.box()
        logging_box.label(text="Logging")
        logging_box.prop(props, "pcp_clear_previous")
        logging_box.prop(props, "pcp_debug_logging_enabled")
        if props.pcp_debug_logging_enabled:
            logging_box.prop(props, "pcp_debug_log_level")
            logging_box.prop(props, "pcp_log_file")


classes = (
    PCP_Properties,
    PCP_OT_generate,
    PCP_PT_main_panel,
)


def register():
    for cls in classes:
        bpy.utils.register_class(cls)
    bpy.types.Scene.pcp = bpy.props.PointerProperty(type=PCP_Properties)


def unregister():
    if hasattr(bpy.types.Scene, "pcp"):
        del bpy.types.Scene.pcp
    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
