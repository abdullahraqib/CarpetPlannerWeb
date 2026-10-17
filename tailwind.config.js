/** @type {import('tailwindcss').Config} */
export default {
  content: ["./index.html", "./src/**/*.{js,jsx,ts,tsx}"],
  theme: {
    extend: {
      fontFamily: {
        // SR Carpets & Floors brand faces (same as srcarpetsandfloors.co.uk)
        sans: ["Barlow", "Helvetica Neue", "Arial", "sans-serif"],
        display: ["Barlow Condensed", "Arial Narrow", "sans-serif"],
      },
      // One step larger than Tailwind's defaults so everything is easy to read.
      fontSize: {
        xs: ["13px", "18px"],
        sm: ["15px", "22px"],
        base: ["17px", "26px"],
        lg: ["20px", "28px"],
        xl: ["24px", "32px"],
      },
      colors: {
        // SR red — 500 is the logo red, 600/700 are the deeper garnet used for buttons and text.
        brand: {
          50: "#fdf3f2",
          100: "#f9dedb",
          500: "#d93732",
          600: "#b8282a",
          700: "#8e1b22",
        },
        ink: {
          800: "#1d1a19",
          900: "#121010",
        },
        // Warm ivory instead of stark white/grey backgrounds — easier on the eyes.
        stone: {
          50: "#f7f3ed",
          100: "#efe9e0",
        },
      },
      keyframes: {
        "fade-in": { from: { opacity: "0" }, to: { opacity: "1" } },
        "pop-in": { from: { opacity: "0", transform: "translateY(8px) scale(0.98)" }, to: { opacity: "1", transform: "none" } },
        "toast-in": { from: { opacity: "0", transform: "translateY(-8px)" }, to: { opacity: "1", transform: "none" } },
      },
      animation: {
        "fade-in": "fade-in 150ms ease-out",
        "pop-in": "pop-in 180ms cubic-bezier(0.2, 0.8, 0.2, 1)",
        "toast-in": "toast-in 220ms cubic-bezier(0.2, 0.8, 0.2, 1)",
      },
    },
  },
  plugins: [],
};
