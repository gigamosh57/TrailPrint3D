import rasterio
from rasterio.plot import show
import matplotlib.pyplot as plt

# Path to your elevation GeoTIFF
tif_path = "/Users/pageweil/Library/CloudStorage/GoogleDrive-gigamosh57@gmail.com/My Drive/3D Printing/TrailPrint3D/.cache/tnm_3dep/b179968d4ea52ccd2deca8c3831f126ece503426.tif"

# Open the raster
with rasterio.open(tif_path) as src:
    elevation = src.read(1)

    # Create plot
    fig, ax = plt.subplots(figsize=(10, 8))

    # Plot elevation data
    show(
        elevation,
        transform=src.transform,
        ax=ax,
        cmap="terrain"
    )

    # Labels and title
    ax.set_title("Elevation Map")
    ax.set_xlabel("Longitude")
    ax.set_ylabel("Latitude")

    # Colorbar
    im = ax.imshow(elevation, cmap="terrain")
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label("Elevation")

plt.show()
